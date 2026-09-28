import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchCauchyKernel
import Mathlib.Analysis.Calculus.ContDiff.Convolution











set_option autoImplicit false

noncomputable section

open Set MeasureTheory Metric
open scoped Topology Convolution ContDiff

namespace PoincareConjecture.M65Branch

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]




def cauchyOperator (h : ℂ → E) (z : ℂ) : E :=
  (Real.pi : ℂ)⁻¹ • ∫ w : ℂ, (z - w)⁻¹ • h w




theorem integrable_cauchyOperator {h : ℂ → E}
    (hh : Continuous h) (hs : HasCompactSupport h) (z : ℂ) :
    Integrable (fun w : ℂ => (z - w)⁻¹ • h w) :=
  (locallyIntegrable_cauchyKernel_sub z).integrable_smul_right_of_hasCompactSupport hh hs




theorem cauchyOperator_eq_convolution (h : ℂ → E) :
    cauchyOperator h = fun z => (Real.pi : ℂ)⁻¹ •
      ((fun w : ℂ => w⁻¹) ⋆[ContinuousLinearMap.lsmul ℝ ℂ, volume] h) z := by
  funext z
  rw [convolution_eq_swap]
  rfl




theorem continuous_cauchyOperator {h : ℂ → E}
    (hh : Continuous h) (hs : HasCompactSupport h) : Continuous (cauchyOperator h) := by
  rw [cauchyOperator_eq_convolution]
  exact (hs.continuous_convolution_right (ContinuousLinearMap.lsmul ℝ ℂ)
    locallyIntegrable_cauchyKernel hh).const_smul _




theorem contDiff_cauchyOperator {h : ℂ → E} {n : ℕ∞}
    (hh : ContDiff ℝ n h) (hs : HasCompactSupport h) :
    ContDiff ℝ n (cauchyOperator h) := by
  rw [cauchyOperator_eq_convolution]
  exact (hs.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℂ)
    locallyIntegrable_cauchyKernel hh).const_smul _




theorem fderiv_cauchyOperator_apply {h : ℂ → E}
    (hh : ContDiff ℝ 1 h) (hs : HasCompactSupport h) (z v : ℂ) :
    fderiv ℝ (cauchyOperator h) z v =
      cauchyOperator (fun w => fderiv ℝ h w v) z := by
  rw [cauchyOperator_eq_convolution]
  have hd := (hs.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℂ)
    locallyIntegrable_cauchyKernel hh z).const_smul (Real.pi : ℂ)⁻¹
  change HasFDerivAt (fun x : ℂ => (Real.pi : ℂ)⁻¹ •
    ((fun w : ℂ => w⁻¹) ⋆[ContinuousLinearMap.lsmul ℝ ℂ, volume] h) x) _ z at hd
  rw [hd.fderiv, smul_apply, convolution_precompR_apply
    (ContinuousLinearMap.lsmul ℝ ℂ) locallyIntegrable_cauchyKernel (hs.fderiv ℝ)
      (hh.continuous_fderiv one_ne_zero)]
  rw [cauchyOperator_eq_convolution]

end PoincareConjecture.M65Branch
