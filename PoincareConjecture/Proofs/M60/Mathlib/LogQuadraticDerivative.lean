import PoincareConjecture.Proofs.M60.Mathlib.SecondLogDerivative
import Mathlib.Analysis.InnerProductSpace.Calculus









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped ContDiff

namespace PoincareConjecture.M60

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]



theorem second_fderiv_log_norm_sq_add (c : ℝ) (hc : 0 < c) (p v : E) :
    fderiv ℝ (fun q => fderiv ℝ (fun r => Real.log (‖r‖ ^ 2 + c)) q v) p v =
      2 * ‖v‖ ^ 2 / (‖p‖ ^ 2 + c) -
        4 * (inner ℝ p v) ^ 2 / (‖p‖ ^ 2 + c) ^ 2 := by
  have hfirst (q : E) : fderiv ℝ (fun r : E => ‖r‖ ^ 2 + c) q v =
      2 * inner ℝ q v := by
    rw [fderiv_add_const, fderiv_norm_sq_apply]
    simp only [two_smul, add_apply, innerSL_apply_apply, two_mul]
  have hd : HasFDerivAt (fun q => 2 * inner ℝ q v) ((2 : ℝ) • innerSL ℝ v) p := by
    convert! (innerSL ℝ v).hasFDerivAt.const_mul 2 using 1
    ext q
    exact congrArg (fun t : ℝ => 2 * t) (real_inner_comm v q)
  have hsecond : fderiv ℝ (fun q => fderiv ℝ (fun r : E => ‖r‖ ^ 2 + c) q v) p v =
      2 * ‖v‖ ^ 2 := by
    simp_rw [hfirst]
    rw [hd.fderiv]
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, real_inner_self_eq_norm_sq]
  rw [second_fderiv_log (((contDiff_norm_sq ℝ).add contDiff_const).contDiffAt)
    (by positivity), hsecond, hfirst]
  ring

end PoincareConjecture.M60
