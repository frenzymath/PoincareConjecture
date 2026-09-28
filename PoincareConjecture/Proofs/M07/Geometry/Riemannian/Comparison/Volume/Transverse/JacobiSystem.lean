import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Transverse.Transport
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Transverse.CurvatureOperator



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

open ConnectionAlongCurve ConnectionVariation

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem hasDerivAt_inverse_parallel_jacobi_operator
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {q : ℝ → M} {I : Set ℝ} {a b t : ℝ}
    (hab : a < b) (hI : IsOpen I)
    (hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ q I) (hsub : Icc a b ⊆ I)
    {P F : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hPi : ∀ s ∈ Icc a b, (P s).IsInvertible)
    (hP : ∀ s ∈ Icc a b, ∀ u,
      ContDiffAt ℝ ∞ (chartField q (q s) (fun r => P r u)) s ∧
      manifoldCovDerivAlong g q (fun r => P r u) 1 s = 0)
    (hF : ∀ s ∈ I, ∀ u,
      ContDiffAt ℝ ∞ (chartField q (q s) (fun r => F r u)) s)
    (hjac : ∀ s ∈ Icc a b, ∀ u,
      manifoldCovDerivAlong g q (manifoldCovDerivAlong g q (fun r => F r u) 1) 1 s =
        -D.curvature (q s) (F s u) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q s 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q s 1))
    (ht : t ∈ Icc a b) :
    let J := fun s => (P s).inverse.comp (F s)
    let K := (P t).inverse.comp ((g.radialCurvatureOperator (q t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)).comp (P t))
    HasDerivAt (deriv J) (-(K.comp (J t))) t := by
  let J := fun s => (P s).inverse.comp (F s)
  let K := (P t).inverse.comp ((g.radialCurvatureOperator (q t)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)).comp (P t))
  change HasDerivAt (deriv J) (-(K.comp (J t))) t
  have hqt (s : ℝ) (hs : s ∈ I) := hq.contMDiffAt (hI.mem_nhds hs)
  have hJ (s : ℝ) (hs : s ∈ Icc a b) : ContDiffAt ℝ ∞ J s := by
    apply contDiffAt_operator_of_apply
    intro u
    exact contDiffAt_inverse_frame_field (hqt s (hsub hs)) (hPi s hs)
      (fun v => (hP s hs v).1) (hF s (hsub hs) u)
  have hval (s : ℝ) (hs : s ∈ Icc a b) (u : EuclideanSpace ℝ (Fin n)) :
      deriv J s u = (P s).inverse (manifoldCovDerivAlong g q (fun r => F r u) 1 s) := by
    have hd := inverse_manifold_parallel_hasDerivAt g hab hs hPi (hqt s (hsub hs))
      (hP s hs) ((hF s (hsub hs) u).differentiableAt (by simp))
    have hdu := ((hJ s hs).differentiableAt (by simp)).hasDerivAt.clm_apply
      (hasDerivAt_const s u)
    simpa only [map_zero, add_zero] using hdu.unique hd
  have hV : ContDiffAt ℝ ∞ (deriv J) t :=
    ((hJ t ht).fderiv_right (by simp)).clm_apply contDiffAt_const
  have hder : deriv (deriv J) t = -(K.comp (J t)) := by
    apply ContinuousLinearMap.ext
    intro u
    have hDJ := contDiffAt_chartField_covDeriv g hI hq
      (fun s hs => hF s hs u) (hsub ht) (mem_extChartAt_source _)
    have hd := inverse_manifold_parallel_hasDerivAt g hab ht hPi (hqt t (hsub ht))
      (hP t ht) (hDJ.differentiableAt (by simp))
    rw [hjac t ht u, map_neg] at hd
    have hdw := hd.hasDerivWithinAt.congr (fun s hs => hval s hs u) (hval t ht u)
    have hvu := (hV.differentiableAt (by simp)).hasDerivAt.clm_apply
      (hasDerivAt_const t u)
    have heq := (hvu.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hab t ht)).symm.trans
      (hdw.derivWithin (uniqueDiffOn_Icc hab t ht))
    simp only [map_zero, add_zero] at heq
    rw [heq]
    change -(P t).inverse (D.curvature (q t) (F t u)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)) =
      -(P t).inverse (g.radialCurvatureOperator (q t)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) (P t ((P t).inverse (F t u))))
    rw [(hPi t ht).self_apply_inverse, g.radialCurvatureOperator_apply D]
  exact hder ▸ (hV.differentiableAt (by simp)).hasDerivAt

end PoincareConjecture.RiemannianMetric
