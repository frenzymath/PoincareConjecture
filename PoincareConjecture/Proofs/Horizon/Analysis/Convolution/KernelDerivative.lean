




import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

open Set MeasureTheory ContinuousLinearMap
open scoped Topology Convolution ContDiff

noncomputable section

namespace Poincare.Analysis.Convolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]



theorem fderiv_convolution_eq_kernel_derivative
    (mu : Measure E) [mu.IsAddHaarMeasure] [mu.IsNegInvariant]
    {f ρ : E → ℝ} (hf : Continuous f) (hρ : ContDiff ℝ 1 ρ)
    (hρc : HasCompactSupport ρ) (x v : E) :
    fderiv ℝ (ρ ⋆[lsmul ℝ ℝ, mu] f) x v =
      ((fun y => fderiv ℝ ρ y v) ⋆[lsmul ℝ ℝ, mu] f) x := by
  have hd := hρc.hasFDerivAt_convolution_right (μ := mu) (lsmul ℝ ℝ)
    hf.locallyIntegrable hρ x
  have hflip : ρ ⋆[lsmul ℝ ℝ, mu] f = f ⋆[lsmul ℝ ℝ, mu] ρ := by
    rw [← convolution_flip]
    funext z
    simp only [convolution_def, flip_apply, lsmul_apply, smul_eq_mul, mul_comm]
  rw [hflip, hd.fderiv]
  rw [convolution_precompR_apply _ hf.locallyIntegrable
    (hρc.fderiv ℝ) (hρ.continuous_fderiv one_ne_zero)]
  rw [convolution_eq_swap]
  simp only [convolution_def, lsmul_apply, smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  exact mul_comm _ _

end Poincare.Analysis.Convolution
