import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution









set_option autoImplicit false

open MeasureTheory Metric Set Filter ContinuousLinearMap
open scoped ContDiff Convolution Topology NNReal

namespace PoincareConjecture.M10

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [Measure.IsAddHaarMeasure μ]


theorem normed_convolution_contDiff (κ : ContDiffBump (0 : E))
    {f : E → ℝ} (hf : Continuous f) :
    ContDiff ℝ ∞ (κ.normed μ ⋆[lsmul ℝ ℝ, μ] f) :=
  κ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
    κ.contDiff_normed hf.locallyIntegrable


theorem dist_normed_convolution_le_lipschitz (κ : ContDiffBump (0 : E))
    {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (x : E) :
    dist ((κ.normed μ ⋆[lsmul ℝ ℝ, μ] f) x) (f x) ≤ L * κ.rOut := by
  apply κ.dist_normed_convolution_le hf.continuous.aestronglyMeasurable
  intro y hy
  exact (hf.dist_le_mul y x).trans
    (mul_le_mul_of_nonneg_left hy.le L.coe_nonneg)


theorem lipschitzWith_normed_convolution (κ : ContDiffBump (0 : E))
    {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    LipschitzWith L (κ.normed μ ⋆[lsmul ℝ ℝ, μ] f) := by
  have hex := (κ.hasCompactSupport_normed (μ := μ)).convolutionExists_left
    (μ := μ) (lsmul ℝ ℝ)
    κ.continuous_normed hf.continuous.locallyIntegrable
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, convolution, convolution, ← integral_sub (hex x) (hex y)]
  calc
    _ ≤ ∫ z, κ.normed μ z * (L * dist x y) ∂μ := by
      apply norm_integral_le_of_norm_le (κ.integrable_normed.mul_const _)
      exact Eventually.of_forall (fun z ↦ by
        simp only [lsmul_apply, smul_eq_mul, ← mul_sub, norm_mul,
          Real.norm_of_nonneg (κ.nonneg_normed z)]
        apply mul_le_mul_of_nonneg_left _ (κ.nonneg_normed z)
        simpa only [← dist_eq_norm, dist_sub_right] using hf.dist_le_mul (x - z) (y - z))
    _ = L * dist x y := by rw [integral_mul_const, κ.integral_normed, one_mul]

end PoincareConjecture.M10
