import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Calibration
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Calibration.ModelAnalytics

/-!
# Static certificates used by the actual analytic estimate

Keep the same cap and compact-component geometry while reading the absolute
analytic bounds of Definition 9.72 and enlarging the constant in Definition
9.75. Sources: Morgan--Tian, pp. 230-232, with the corrected outer absolute
value recorded in the September 18 Definition 9.72 review.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M]
  {g : RiemannianMetric 3 M} {D : LeviCivitaData g}

/-- The certificate keeps its exact carrier when its geometric constant grows. -/
noncomputable def SingularCComponent.mono_constant {C C' : ℝ}
    (N : SingularCComponent g D C) (hCC' : C ≤ C') :
    SingularCComponent g D C' := by
  have hC' : 0 < C' := N.constant_pos.trans_le hCC'
  have hinv : C'⁻¹ ≤ C⁻¹ := (inv_le_inv₀ hC' N.constant_pos).2 hCC'
  refine { N with
    constant_pos := hC'
    sectional_lower := ?_
    diameter_lower := ?_
    diameter_upper := ?_ }
  · intro x hx v w hvw
    by_cases hsup : 0 ≤ scalarCurvatureSupOn g D N.carrier
    · exact (mul_le_mul_of_nonneg_right hinv hsup).trans_lt
        (N.sectional_lower x hx v w hvw)
    · exact (mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hC'.le)
        (le_of_not_ge hsup)).trans_lt (N.positive_sectional x hx v w hvw)
  · apply lt_of_le_of_lt _ N.diameter_lower
    rw [ENNReal.ofReal_mul (inv_nonneg.mpr hC'.le),
      ENNReal.ofReal_mul (inv_nonneg.mpr N.constant_pos.le)]
    gcongr
  · apply lt_of_lt_of_le N.diameter_upper
    rw [ENNReal.ofReal_mul N.constant_pos.le, ENNReal.ofReal_mul hC'.le]
    gcongr

omit [T2Space M] [SecondCountableTopology M] in
/-- Uniform supremum witnesses give the pointwise absolute estimates on the core. -/
theorem CapCertificate.core_analytic (N : CapCertificate g) (x : M)
    (hx : x ∈ N.core) :
    M45PointwiseAnalyticEstimate g N.connection x N.cap_constant := by
  have hc : x ∈ N.closed_core := by
    rw [N.core_eq_interior_closed_core] at hx
    exact interior_subset hx
  rw [N.closed_core_eq_complement_end] at hc
  have hpos := N.scalar_pos x hc.1
  obtain ⟨G, hG, hg⟩ := N.gradient_bound
  obtain ⟨L, hL, hl⟩ := N.laplacian_bound
  exact ⟨hpos,
    (hg x hc.1).trans (mul_le_mul_of_nonneg_right hG.le (Real.rpow_nonneg hpos.le _)),
    (hl x hc.1).trans (mul_le_mul_of_nonneg_right hL.le (sq_nonneg _))⟩

end PoincareMT
