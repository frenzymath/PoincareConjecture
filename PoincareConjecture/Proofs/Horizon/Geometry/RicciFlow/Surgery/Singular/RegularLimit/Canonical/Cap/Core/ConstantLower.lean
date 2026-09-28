import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Bounds
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.DistanceLower







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}



theorem sqrt_mul_inverse_epsilon_lt_constant (C : CapCertificate g) :
    Real.sqrt (1 - C.epsilon) * C.epsilon⁻¹ < C.cap_constant := by
  obtain ⟨x, hx⟩ := C.core_nonempty
  have hxclosed : x ∈ C.closed_core := C.core_subset_closed_core hx
  have hxout : x ∉ C.end_neck.carrier := by
    rw [C.closed_core_eq_complement_end] at hxclosed
    exact hxclosed.2
  have hlow := C.end_neck.edist_center_lower_of_not_mem_carrier hxout
  have hhigh := C.edist_lt_at_point (le_refl C.cap_constant)
    (C.end_neck_subset (C.end_neck.central_sphere_subset
      C.end_neck.center_on_central_sphere)) (C.core_subset_carrier hx)
  rw [← C.end_neck_connection, ← C.end_neck.scale_eq_scalar] at hhigh
  have hreal := (ENNReal.ofReal_lt_ofReal_iff
    (mul_pos C.cap_constant_pos C.end_neck.scale_pos)).mp (hlow.trans_lt hhigh)
  rw [C.end_neck_epsilon] at hreal
  nlinarith [C.end_neck.scale_pos]


theorem inverse_epsilon_mul_ninetyNine_lt_constant (C : CapCertificate g) :
    (0.99 : ℝ) * C.epsilon⁻¹ < C.cap_constant := by
  have hroot : (0.99 : ℝ) ≤ Real.sqrt (1 - C.epsilon) := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 - C.epsilon by
      linarith [C.epsilon_le_threshold])
    nlinarith [Real.sqrt_nonneg (1 - C.epsilon), C.epsilon_le_threshold]
  exact (mul_le_mul_of_nonneg_right hroot (inv_pos.mpr C.epsilon_pos).le).trans_lt
    C.sqrt_mul_inverse_epsilon_lt_constant

theorem oneHundredNinetyEight_lt_constant (C : CapCertificate g) :
    198 < C.cap_constant := by
  have hinv : 200 ≤ C.epsilon⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ C.epsilon_pos).mpr
    linarith [C.epsilon_le_threshold]
  have h := C.inverse_epsilon_mul_ninetyNine_lt_constant
  linarith

end PoincareConjecture.CapCertificate
