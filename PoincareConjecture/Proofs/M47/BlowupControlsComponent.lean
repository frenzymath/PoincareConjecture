import PoincareConjecture.Proofs.M47.ComponentEstimateGeometry









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M47



noncomputable def component_relax_constant
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} {D : LeviCivitaData g} {C C' : ℝ}
    (N : SingularCComponent g D C) (hC : C ≤ C') : SingularCComponent g D C' := by
  have hinverse : C'⁻¹ ≤ C⁻¹ := inv_anti₀ N.constant_pos hC
  have hscalar : 0 ≤ scalarCurvatureSupOn g D N.carrier := by
    apply Real.sSup_nonneg
    rintro _ ⟨x, rfl⟩
    exact (component_scalar_pos N x.property).le
  have hradius : ∀ r ∈ range (fun x : N.carrier =>
      D.scalarCurvature x.val ^ (-1 / 2 : ℝ)), 0 ≤ r := by
    rintro _ ⟨x, rfl⟩
    exact Real.rpow_nonneg (component_scalar_pos N x.property).le _
  exact {
    constant_pos := N.constant_pos.trans_le hC
    basepoint := N.basepoint
    carrier := N.carrier
    component_eq := N.component_eq
    compact := N.compact
    topology := N.topology
    positive_sectional := N.positive_sectional
    sectional_lower := fun x hx v w hvw =>
      (mul_le_mul_of_nonneg_right hinverse hscalar).trans_lt
        (N.sectional_lower x hx v w hvw)
    diameter_lower :=
      (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hinverse (Real.sSup_nonneg hradius))).trans_lt
          N.diameter_lower
    diameter_upper := N.diameter_upper.trans_le
      (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hC (Real.sInf_nonneg hradius)))
  }

end PoincareConjecture.M47
