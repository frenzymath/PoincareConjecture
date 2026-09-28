import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Frame.Curvature
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Orthonormal
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Variation.Intrinsic
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Index.Negative



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Bundle

namespace PoincareConjecture.ConjugateFrame

open ConnectionAlongCurve ConnectionVariation CoordinateExponential

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem exists_orthonormal_parallel_transport
    (g : RiemannianMetric n M)
    {q : ℝ → M} {I : Set ℝ} {a b : ℝ} (hab : a < b)
    (hI : IsOpen I) (hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ q I)
    (hsub : Icc a b ⊆ I) :
    ∃ P : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
      (∀ t ∈ Icc a b, (P t).IsInvertible) ∧
      (∀ t ∈ Icc a b, ∀ u,
        ContDiffAt ℝ ∞ (chartField q (q t) (fun s => P s u)) t ∧
        manifoldCovDerivAlong g q (fun s => P s u) 1 t = 0) ∧
      ∀ t ∈ Icc a b, ∀ u v,
        g.inner (q t) (P t u) (P t v) = inner ℝ u v := by
  obtain ⟨Q, _, hQi, hQ, hpair⟩ := exists_manifold_parallel_transport g hab hI hq hsub
  obtain ⟨L, hL⟩ := g.exists_orthonormal_coordinate_frame (q a)
  refine ⟨fun t => (Q t).comp L.toContinuousLinearMap, ?_, ?_, ?_⟩
  · exact fun t ht => (hQi t ht).comp ⟨L, rfl⟩
  · exact fun t ht u => hQ t ht (L u)
  · intro t ht u v
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ← g.chartCoefficients_center] using (hpair t ht (L u) (L v)).trans
        (by simpa only [g.chartCoefficients_center] using hL u v)

omit [IsManifold (𝓡 n) ∞ M] in
theorem contDiffAt_frame_field
    {q : ℝ → M} {P : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {W : ℝ → EuclideanSpace ℝ (Fin n)} {a : M} {t : ℝ}
    (hP : ∀ u, ContDiffAt ℝ ∞ (chartField q a (fun s => P s u)) t)
    (hW : ContDiffAt ℝ ∞ W t) :
    ContDiffAt ℝ ∞ (chartField q a (fun s => P s (W s))) t := by
  let Q := fun s => (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a) (q s)).comp (P s)
  have hQ : ContDiffAt ℝ ∞ Q t := contDiffAt_operator_of_apply hP
  exact hQ.clm_apply hW

theorem covDeriv_frame_field
    {q : ℝ → M} {P : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {W : ℝ → EuclideanSpace ℝ (Fin n)} {a b t : ℝ}
    (ht : t ∈ Ioo a b)
    (hi : ∀ s ∈ Icc a b, (P s).IsInvertible)
    (hq : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ q t)
    (hP : ∀ u, ContDiffAt ℝ ∞ (chartField q (q t) (fun s => P s u)) t ∧
      manifoldCovDerivAlong g q (fun s => P s u) 1 t = 0)
    (hW : ContDiffAt ℝ ∞ W t) :
    manifoldCovDerivAlong g q (fun s => P s (W s)) 1 t = P t (deriv W t) := by
  have hV := contDiffAt_frame_field (fun u => (hP u).1) hW
  have hd := inverse_manifold_parallel_hasDerivAt g (ht.1.trans ht.2)
    (Ioo_subset_Icc_self ht) hi hq hP (hV.differentiableAt (by simp))
  have heq : (fun s => (P s).inverse (P s (W s))) =ᶠ[𝓝 t] W := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    exact (hi s hs).inverse_apply_self (W s)
  have hd' := (hd.congr_of_eventuallyEq heq.symm).deriv
  have hp := congrArg (P t) hd'
  rw [(hi t (Ioo_subset_Icc_self ht)).self_apply_inverse] at hp
  exact hp.symm

theorem contDiffAt_inverse_frame_field
    {q : ℝ → M} {P : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {J : (s : ℝ) → TangentSpace (𝓡 n) (q s)} {t : ℝ}
    (hi : (P t).IsInvertible)
    (hq : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ q t)
    (hP : ∀ u, ContDiffAt ℝ ∞ (chartField q (q t) (fun s => P s u)) t)
    (hJ : ContDiffAt ℝ ∞ (chartField q (q t) J) t) :
    ContDiffAt ℝ ∞ (fun s => (P s).inverse (J s)) t := by
  let L : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    fun s => mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) (q t)) (q s)
  let Q := fun s => (L s).comp (P s)
  have hL : (L t).IsInvertible := isInvertible_mfderiv_extChartAt (mem_extChartAt_source _)
  have hQ : ContDiffAt ℝ ∞ Q t := contDiffAt_operator_of_apply hP
  have hInv := ((hL.comp hi).contDiffAt_map_inverse (n := ∞)).comp t hQ
  have hrep : (fun s => (P s).inverse (J s)) =ᶠ[𝓝 t]
      fun s => (Q s).inverse (chartField q (q t) J s) := by
    filter_upwards [hq.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := 𝓡 n) (q t)).mem_nhds (mem_extChartAt_source _))]
      with s hs
    have hLs : (L s).IsInvertible := isInvertible_mfderiv_extChartAt hs
    change (P s).inverse (J s) = ((L s).comp (P s)).inverse (L s (J s))
    rw [hLs.inverse_comp_apply_of_left, hLs.inverse_apply_self]
  exact (hInv.clm_apply hJ).congr_of_eventuallyEq hrep

theorem indexIntegrand_frame_field (D : LeviCivitaData g)
    {q : ℝ → M} {P : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {W : ℝ → EuclideanSpace ℝ (Fin n)} {a b t : ℝ}
    (ht : t ∈ Ioo a b)
    (hi : ∀ s ∈ Icc a b, (P s).IsInvertible)
    (hq : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ q t)
    (hP : ∀ u, ContDiffAt ℝ ∞ (chartField q (q t) (fun s => P s u)) t ∧
      manifoldCovDerivAlong g q (fun s => P s u) 1 t = 0)
    (hp : ∀ u v, g.inner (q t) (P t u) (P t v) = inner ℝ u v)
    (hW : ContDiffAt ℝ ∞ W t) :
    ConjugateVariation.intrinsicIndexIntegrand g D q (fun s => P s (W s)) t =
      Poincare.ODE.Jacobi.indexIntegrand (coefficient g q P) W (deriv W) W (deriv W) t := by
  unfold ConjugateVariation.intrinsicIndexIntegrand Poincare.ODE.Jacobi.indexIntegrand
  rw [covDeriv_frame_field ht hi hq hP hW, hp]
  congr 1
  simp only [coefficient, chartCoefficient_apply D P (mem_extChartAt_source _) hq]
  rw [← hp, (hi t (Ioo_subset_Icc_self ht)).self_apply_inverse]

end PoincareConjecture.ConjugateFrame
