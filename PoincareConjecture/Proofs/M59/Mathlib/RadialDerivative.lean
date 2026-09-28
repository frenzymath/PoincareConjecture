import PoincareConjecture.Proofs.M58.Mathlib.RadialNormalization









set_option autoImplicit false

open scoped RealInnerProductSpace

namespace PoincareConjecture.Proofs.M59

open M58

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]




theorem fderiv_radialNormalization_unit {x : E} (hx : ‖x‖ = 1) (v : E) :
    fderiv ℝ radialNormalization x v = v - ⟪x, v⟫ • x := by
  have hnorm : HasFDerivAt (fun y : E => ‖y‖) (innerSL ℝ x) x := by
    have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (by rw [hx]; norm_num)
    simp only [Real.sqrt_sq_eq_abs, abs_norm] at h
    convert h using 1
    ext y
    simp [hx]
  have hinv := (hasDerivAt_inv (by rw [hx]; exact one_ne_zero)).comp_hasFDerivAt x hnorm
  have hrad : HasFDerivAt (fun y : E => ‖y‖⁻¹ • y) _ x :=
    hinv.smul (hasFDerivAt_id x)
  change fderiv ℝ (fun y : E => ‖y‖⁻¹ • y) x v = _
  rw [hrad.fderiv]
  simp [hx, sub_eq_add_neg]

end PoincareConjecture.Proofs.M59
