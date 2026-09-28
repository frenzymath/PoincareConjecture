import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox









set_option autoImplicit false

open ContinuousLinearMap MeasureTheory
open scoped Convolution NNReal ContDiff

namespace Poincare

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]


theorem lipschitzWith_normed_convolution {f : E → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (φ : ContDiffBump (0 : E)) :
    LipschitzWith K (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) := by
  have hi : ConvolutionExists (φ.normed μ) f (lsmul ℝ ℝ) μ :=
    φ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right
      (lsmul ℝ ℝ) (φ.contDiff_normed (n := 0)).continuous.locallyIntegrable hf.continuous
  simp only [ConvolutionExists, ConvolutionExistsAt, lsmul_apply, smul_eq_mul] at hi
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq, convolution_def, lsmul_apply, smul_eq_mul]
  rw [← integral_sub (hi x) (hi y)]
  calc
    |∫ t, φ.normed μ t * f (x - t) - φ.normed μ t * f (y - t) ∂μ|
        ≤ ∫ t, |φ.normed μ t * f (x - t) - φ.normed μ t * f (y - t)| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ t, φ.normed μ t * (K * dist x y) ∂μ := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun _ ↦ abs_nonneg _
      · exact φ.integrable_normed.mul_const _
      · apply Filter.Eventually.of_forall
        intro t
        dsimp only
        rw [← mul_sub, abs_mul, abs_of_nonneg (φ.nonneg_normed t)]
        apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed t)
        simpa only [Real.dist_eq, dist_sub_right] using hf.dist_le_mul (x - t) (y - t)
    _ = K * dist x y := by rw [integral_mul_const, φ.integral_normed, one_mul]


theorem dist_normed_convolution_le_radius {f : E → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (φ : ContDiffBump (0 : E)) (x : E) :
    dist ((φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) x) (f x) ≤ K * φ.rOut := by
  apply φ.dist_normed_convolution_le hf.continuous.aestronglyMeasurable
  intro y hy
  exact (hf.dist_le_mul y x).trans
    (mul_le_mul_of_nonneg_left (Metric.mem_ball.mp hy).le K.coe_nonneg)


theorem norm_fderiv_normed_convolution_le {f : E → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (φ : ContDiffBump (0 : E)) (x : E) :
    ‖fderiv ℝ (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) x‖ ≤ K :=
  norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_normed_convolution μ hf φ)

end Poincare

namespace Poincare



theorem exists_contDiff_lipschitz_approx
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : E → ℝ, ContDiff ℝ ∞ u ∧ LipschitzWith K u ∧
      (∀ x, dist (u x) (f x) ≤ ε) ∧ (∀ x, ‖fderiv ℝ u x‖ ≤ K) := by
  borelize E
  let μ : Measure E := Measure.addHaar
  let r : ℝ := ε / (K + 1)
  have hr : 0 < r := div_pos hε (by positivity)
  let φ : ContDiffBump (0 : E) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  refine ⟨φ.normed μ ⋆[lsmul ℝ ℝ, μ] f, ?_,
    lipschitzWith_normed_convolution μ hf φ, ?_,
    norm_fderiv_normed_convolution_le μ hf φ⟩
  · exact φ.hasCompactSupport_normed.contDiff_convolution_left _
      φ.contDiff_normed hf.continuous.locallyIntegrable
  · intro x
    apply (dist_normed_convolution_le_radius μ hf φ x).trans
    change (K : ℝ) * r ≤ ε
    have heq : r * (K + 1) = ε := div_mul_cancel₀ _ (by positivity)
    nlinarith

end Poincare
