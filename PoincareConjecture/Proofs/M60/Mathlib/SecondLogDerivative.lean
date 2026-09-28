import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M60

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem second_fderiv_log {a : E → ℝ} {p : E}
    (ha : ContDiffAt ℝ 2 a p) (hp : a p ≠ 0) (v : E) :
    fderiv ℝ (fun q => fderiv ℝ (fun r => Real.log (a r)) q v) p v =
      fderiv ℝ (fun q => fderiv ℝ a q v) p v / a p -
        (fderiv ℝ a p v) ^ 2 / (a p) ^ 2 := by
  have hda : ContDiffAt ℝ 1 (fun q => fderiv ℝ a q v) p :=
    (ha.fderiv_right (by norm_num)).clm_apply contDiffAt_const
  have heq : (fun q => fderiv ℝ (fun r => Real.log (a r)) q v) =ᶠ[𝓝 p]
      (fun q => fderiv ℝ a q v / a q) := by
    filter_upwards [ha.eventually (by norm_num), ha.continuousAt.eventually_ne hp]
      with q hq hnq
    rw [((hq.differentiableAt (by norm_num)).hasFDerivAt.log hnq).fderiv]
    simp only [smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hd := (hda.differentiableAt (by norm_num)).hasFDerivAt.mul
    ((hasDerivAt_inv hp).comp_hasFDerivAt p (ha.differentiableAt (by norm_num)).hasFDerivAt)
  dsimp only [Pi.mul_apply, Function.comp_def] at hd
  change HasFDerivAt (fun q => fderiv ℝ a q v * (a q)⁻¹) _ p at hd
  rw [heq.fderiv_eq]
  simp only [div_eq_mul_inv]
  rw [hd.fderiv]
  simp only [smul_apply, add_apply, smul_eq_mul]
  ring

end PoincareConjecture.M60
