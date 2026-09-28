import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchGaugeSeries
import Mathlib.Analysis.Complex.Conformal











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Complex
open scoped Topology ContDiff

namespace PoincareConjecture.M65Branch

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]




theorem differentiableAt_complex_of_dbar_eq_zero {f : ℂ → E} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hz : dbar f z = 0) : DifferentiableAt ℂ f z := by
  apply differentiableAt_complex_iff_differentiableAt_real.mpr
  refine ⟨hf, ?_⟩
  have hsum : fderiv ℝ f z 1 + I • fderiv ℝ f z I = 0 := by
    change (2 : ℂ)⁻¹ • (fderiv ℝ f z 1 + I • fderiv ℝ f z I) = 0 at hz
    exact (smul_eq_zero.mp hz).resolve_left (inv_ne_zero (by norm_num))
  have hI := congrArg (fun v : E => I • v) hsum
  simp only [smul_add, smul_smul, I_mul_I, neg_one_smul, smul_zero] at hI
  exact (eq_of_sub_eq_zero (show I • fderiv ℝ f z 1 - fderiv ℝ f z I = 0 by
    simpa only [sub_eq_add_neg] using hI)).symm




theorem dbar_clm_apply {P : ℂ → E →L[ℂ] E} {F : ℂ → E} {z : ℂ}
    (hP : DifferentiableAt ℝ P z) (hF : DifferentiableAt ℝ F z) :
    dbar (fun w => P w (F w)) z = dbar P z (F z) + P z (dbar F z) := by
  let L := ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ
  have hR := L.hasFDerivAt.comp z hP.hasFDerivAt
  have hD := hR.clm_apply hF.hasFDerivAt
  have hactual (v : ℂ) : fderiv ℝ (fun w => P w (F w)) z v =
      P z (fderiv ℝ F z v) + fderiv ℝ P z v (F z) := by
    exact congrArg (fun D : ℂ →L[ℝ] E => D v) hD.fderiv
  simp only [dbar, dbarLinear, smul_apply, add_apply, ContinuousLinearMap.apply_apply,
    hactual, map_add, map_smul]
  module

end PoincareConjecture.M65Branch
