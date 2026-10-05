import PoincareLib.Geometry.CurveShortening.Deformation.MinimalDisk.Branch.Cauchy.Kernel
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# The genuine compact-support Cauchy operator

The literal inverse-kernel integral is a locally integrable convolution.
Its continuity and actual derivatives follow from compact support of the
forcing. Source: Eschenburg--Tribuzy, Conformal mappings of surfaces and
Cauchy--Riemann inequalities, preprint pp. 8--11; M65 derivation 32,
fifth consumer, for MT Lemma 19.2, printed pp. 438--439.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Metric
open scoped Topology Convolution ContDiff

namespace PoincareMT.M65Branch

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The literal Cauchy integral. Its integrability for actual compact
continuous forcing is proved below. Source: Eschenburg--Tribuzy,
preprint pp. 8--11; M65 derivation 32, fifth consumer. -/
def cauchyOperator (h : ℂ → E) (z : ℂ) : E :=
  (Real.pi : ℂ)⁻¹ • ∫ w : ℂ, (z - w)⁻¹ • h w

/-- The genuine compact-support Cauchy integrand is integrable.
Source: Eschenburg--Tribuzy, preprint pp. 8--11;
M65 derivation 32, fifth consumer. -/
theorem integrable_cauchyOperator {h : ℂ → E}
    (hh : Continuous h) (hs : HasCompactSupport h) (z : ℂ) :
    Integrable (fun w : ℂ => (z - w)⁻¹ • h w) :=
  (locallyIntegrable_cauchyKernel_sub z).integrable_smul_right_of_hasCompactSupport hh hs

/-- Translation identifies the literal Cauchy integral with the actual
locally integrable convolution. Source: Eschenburg--Tribuzy,
preprint pp. 8--11; M65 derivation 32, fifth consumer. -/
theorem cauchyOperator_eq_convolution (h : ℂ → E) :
    cauchyOperator h = fun z => (Real.pi : ℂ)⁻¹ •
      ((fun w : ℂ => w⁻¹) ⋆[ContinuousLinearMap.lsmul ℝ ℂ, volume] h) z := by
  funext z
  rw [convolution_eq_swap]
  rfl

/-- Actual compact continuous forcing produces a continuous Cauchy
integral. Source: Eschenburg--Tribuzy, preprint pp. 8--11;
M65 derivation 32, fifth consumer. -/
theorem continuous_cauchyOperator {h : ℂ → E}
    (hh : Continuous h) (hs : HasCompactSupport h) : Continuous (cauchyOperator h) := by
  rw [cauchyOperator_eq_convolution]
  exact (hs.continuous_convolution_right (ContinuousLinearMap.lsmul ℝ ℂ)
    locallyIntegrable_cauchyKernel hh).const_smul _

/-- The actual Cauchy operator inherits every given real smoothness
order from compactly supported forcing. Source: Eschenburg--Tribuzy,
preprint pp. 8--11; M65 derivation 32, fifth consumer. -/
theorem contDiff_cauchyOperator {h : ℂ → E} {n : ℕ∞}
    (hh : ContDiff ℝ n h) (hs : HasCompactSupport h) :
    ContDiff ℝ n (cauchyOperator h) := by
  rw [cauchyOperator_eq_convolution]
  exact (hs.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℂ)
    locallyIntegrable_cauchyKernel hh).const_smul _

/-- The actual real derivative commutes with the compact-support Cauchy
operator. Source: Eschenburg--Tribuzy, preprint pp. 8--11;
M65 derivation 32, fifth consumer. -/
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

end PoincareMT.M65Branch
