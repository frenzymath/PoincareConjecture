import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

set_option autoImplicit false

namespace PoincareConjecture.M10

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem normalized_metric_vector_norm_sq_le (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hi : B.IsInvertible) (C : E ≃L[ℝ] E)
    (hC : ∀ v w, B (C v) (C w) = inner ℝ v w) (v : E) :
    ‖C v‖ ^ 2 ≤ ‖B.inverse‖ * ‖v‖ ^ 2 := by
  let β := C v
  let z := B.inverse (innerSL ℝ β)
  have hz (w : E) : B z w = inner ℝ β w := by
    exact congrArg (fun d : E →L[ℝ] ℝ ↦ d w) (hi.self_apply_inverse (innerSL ℝ β))
  have hnz : ‖z‖ ≤ ‖B.inverse‖ * ‖β‖ := by
    simpa only [innerSL_apply_norm] using B.inverse.le_opNorm (innerSL ℝ β)
  have hcross : inner ℝ (C.symm z) v = B z β := by
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using (hC (C.symm z) v).symm
  have hself : inner ℝ (C.symm z) (C.symm z) = B z z := by
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using
      (hC (C.symm z) (C.symm z)).symm
  have hcs := real_inner_mul_inner_self_le (C.symm z) v
  rw [hcross, hself, hz β, hz z, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq] at hcs
  have hzz : inner ℝ β z ≤ ‖B.inverse‖ * ‖β‖ ^ 2 := calc
    inner ℝ β z ≤ ‖β‖ * ‖z‖ := real_inner_le_norm _ _
    _ ≤ ‖β‖ * (‖B.inverse‖ * ‖β‖) := mul_le_mul_of_nonneg_left hnz (norm_nonneg β)
    _ = ‖B.inverse‖ * ‖β‖ ^ 2 := by ring
  have hbound := hcs.trans (mul_le_mul_of_nonneg_right hzz (sq_nonneg ‖v‖))
  by_cases hβ : β = 0
  · change ‖β‖ ^ 2 ≤ _
    simp only [hβ, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity
  · have hpos : 0 < ‖β‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hβ)
    change ‖β‖ ^ 2 ≤ _
    apply (mul_le_mul_iff_right₀ hpos).mp
    nlinarith [hbound]

end PoincareConjecture.M10
