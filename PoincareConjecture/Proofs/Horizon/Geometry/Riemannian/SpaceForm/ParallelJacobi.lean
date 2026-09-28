import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Jacobi
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.AlongCurve.Manifold

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.SpaceForm

open ConnectionAlongCurve ConnectionVariation

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem exists_parallel_spherical_jacobi
    (D : LeviCivitaData g) {q : ℝ → M} {I : Set ℝ} {b : ℝ}
    (hb : 0 < b) (hI : IsOpen I)
    (hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ q I) (hsub : Icc 0 b ⊆ I)
    (V J : (t : ℝ) → TangentSpace (𝓡 n) (q t))
    (hV : ∀ t ∈ I, ContDiffAt ℝ ∞ (chartField q (q t) V) t)
    (hparallel : ∀ t ∈ Icc 0 b, manifoldCovDerivAlong g q V 1 t = 0)
    (hunit : g.inner (q 0) (V 0) (V 0) = 1)
    (hJ : ∀ t ∈ I, ContDiffAt ℝ ∞ (chartField q (q t) J) t)
    (hjac : ∀ t ∈ Icc 0 b,
      manifoldCovDerivAlong g q (manifoldCovDerivAlong g q J 1) 1 t =
        -D.curvature (q t) (J t) (V t) (V t))
    (hsec : ∀ t ∈ Icc 0 b, ∀ u v : TangentSpace (𝓡 n) (q t),
      g.inner (q t) u u * g.inner (q t) v v - (g.inner (q t) u v) ^ 2 ≠ 0 →
        D.sectionalCurvature (q t) u v = 1)
    (hJ0 : J 0 = 0)
    (hnormal : g.inner (q 0) (manifoldCovDerivAlong g q J 1 0) (V 0) = 0) :
    ∃ P : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
      P 0 = ContinuousLinearMap.id ℝ _ ∧
      (∀ t ∈ Icc 0 b, (P t).IsInvertible) ∧
      (∀ t ∈ Icc 0 b, ∀ u v,
        g.inner (q t) (P t u) (P t v) = g.inner (q 0) u v) ∧
      (∀ t ∈ Icc 0 b, J t = Real.sin t • P t (manifoldCovDerivAlong g q J 1 0)) ∧
      ∀ t ∈ Icc 0 b, manifoldCovDerivAlong g q J 1 t =
        Real.cos t • P t (manifoldCovDerivAlong g q J 1 0) := by
  obtain ⟨P, hP0, hPi, hP, hpair⟩ := exists_manifold_parallel_transport g hb hI hq hsub
  have hqt (t : ℝ) (ht : t ∈ I) := hq.contMDiffAt (hI.mem_nhds ht)
  have hVconst (t : ℝ) (ht : t ∈ Icc 0 b) : (P t).inverse (V t) = V 0 := by
    have hd (s : ℝ) (hs : s ∈ Icc 0 b) :
        HasDerivWithinAt (fun r => (P r).inverse (V r)) 0 (Icc 0 b) s := by
      have h := inverse_manifold_parallel_hasDerivAt g hb hs hPi (hqt s (hsub hs))
        (hP s hs) ((hV s (hsub hs)).differentiableAt (by simp))
      simpa only [hparallel s hs, map_zero] using h.hasDerivWithinAt
    have hc := constant_of_derivWithin_zero (fun s hs => (hd s hs).differentiableWithinAt)
      (fun s hs => (hd s ⟨hs.1, hs.2.le⟩).derivWithin
        (uniqueDiffOn_Icc hb s ⟨hs.1, hs.2.le⟩)) t ht
    simpa only [hP0, ContinuousLinearMap.inverse_id, ContinuousLinearMap.id_apply] using hc
  have hPV (t : ℝ) (ht : t ∈ Icc 0 b) : P t (V 0) = V t := by
    rw [← hVconst t ht, (hPi t ht).self_apply_inverse]
  let A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearMap.id ℝ _ - (g.inner (q 0) (V 0)).smulRight (V 0)
  have hA (t : ℝ) (ht : t ∈ Icc 0 b) (u : EuclideanSpace ℝ (Fin n)) :
      (P t).inverse (D.curvature (q t) (P t u) (V t) (V t)) = A u := by
    have hr := D.radialCurvature_of_constant_sectional (q t) 1 (hsec t ht) (V t) (P t u)
    change D.curvature (q t) (P t u) (V t) (V t) = _ at hr
    rw [hr, one_smul, ← hPV t ht, hpair t ht, hpair t ht, hunit, one_smul,
      map_sub, map_smul, (hPi t ht).inverse_apply_self, (hPi t ht).inverse_apply_self]
    dsimp only [A]
    rw [g.symm (q 0) u (V 0)]
    rfl
  let y := fun t => (P t).inverse (J t)
  let v := fun t => (P t).inverse (manifoldCovDerivAlong g q J 1 t)
  have hsol : Poincare.ODE.Jacobi.IsJacobiSolOn (fun _ => A) 0 b y v := by
    constructor
    · intro t ht
      exact (inverse_manifold_parallel_hasDerivAt g hb ht hPi (hqt t (hsub ht))
        (hP t ht) ((hJ t (hsub ht)).differentiableAt (by simp))).hasDerivWithinAt
    · intro t ht
      have hDJ := contDiffAt_chartField_covDeriv g hI hq hJ (hsub ht) (mem_extChartAt_source _)
      have hd := inverse_manifold_parallel_hasDerivAt g hb ht hPi (hqt t (hsub ht))
        (hP t ht) (hDJ.differentiableAt (by simp))
      rw [hjac t ht, map_neg] at hd
      have heq := hA t ht ((P t).inverse (J t))
      rw [(hPi t ht).self_apply_inverse] at heq
      rw [heq] at hd
      exact hd.hasDerivWithinAt
  let w := manifoldCovDerivAlong g q J 1 0
  have hw : A w = (1 : ℝ) ^ 2 • w := by
    have hn : g.inner (q 0) (V 0) w = 0 := (g.symm _ _ _).trans hnormal
    change w - g.inner (q 0) (V 0) w • V 0 = (1 : ℝ) ^ 2 • w
    rw [hn]
    simp
  have hformula (t : ℝ) (ht : t ∈ Icc 0 b) :
      y t = Real.sin t • w ∧ v t = Real.cos t • w := by
    have h := hsol.eq_spherical (c := 1) (by norm_num) (w₀ := 0) (by simp) hw
      (by simp [y, hJ0]) (by simp [v, w, hP0]) ht
    simpa using h
  refine ⟨P, hP0, hPi, hpair, ?_, ?_⟩
  · intro t ht
    have h := congrArg (P t) (hformula t ht).1
    simpa only [y, (hPi t ht).self_apply_inverse, map_smul] using h
  · intro t ht
    have h := congrArg (P t) (hformula t ht).2
    simpa only [v, (hPi t ht).self_apply_inverse, map_smul] using h

end PoincareConjecture.SpaceForm
