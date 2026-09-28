import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.CurvatureNullity
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.RicciBounds


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.LeviCivitaData

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}



theorem exists_null_plane_of_not_ricci_positive
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (hoperator : ∀ x, D.NonnegativeCurvatureOperator x)
    (hnot : ¬ ∀ x : M, ∀ v : TangentSpace (𝓡 3) x, v ≠ 0 →
      0 < D.ricci x v v) :
    ∃ (x : M) (v w : TangentSpace (𝓡 3) x),
      g.inner x v v = 1 ∧ g.inner x w w = 1 ∧ g.inner x v w = 0 ∧
        D.curvatureTensor x v w v w = 0 := by
  push Not at hnot
  obtain ⟨x, v, hv, hRic⟩ := hnot
  have hzero : D.ricci x v v = 0 :=
    le_antisymm hRic (D.ricci_bounds_of_nonnegative_curvatureOperator hD x
      (hoperator x) v).1
  have hcurv := RicciFlow.Splitting.curvatureTensor_eq_zero_of_ricci_self_eq_zero
    D hD x (fun u w => D.curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      x (hoperator x) u w) hzero
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) := by
    unfold TangentSpace
    infer_instance
  let u := (‖v‖⁻¹ : ℝ) • v
  have hu : inner ℝ u u = 1 := by
    rw [real_inner_self_eq_norm_sq]
    have hn : ‖u‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hv
    rw [hn, one_pow]
  have hframe : Orthonormal ℝ (({0} : Set (Fin 3)).domRestrict (fun _ => u)) := by
    apply orthonormal_iff_ite.mpr
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    have hi' : i = 0 := hi
    have hj' : j = 0 := hj
    subst i
    subst j
    simpa using hu
  obtain ⟨b, hb⟩ := hframe.exists_orthonormalBasis_extension_of_card_eq
    (show Module.finrank ℝ (TangentSpace (𝓡 3) x) = Fintype.card (Fin 3) from
      finrank_euclideanSpace_fin)
  have hb0 : b 0 = u := hb 0 (by simp)
  refine ⟨x, b 0, b 1, ?_, ?_, ?_, ?_⟩
  · exact b.inner_eq_ite 0 0
  · exact b.inner_eq_ite 1 1
  · exact b.inner_eq_ite 0 1
  · rw [hb0]
    simp only [u, D.curvatureTensor_smul_first, hcurv, mul_zero]

end PoincareConjecture.LeviCivitaData
