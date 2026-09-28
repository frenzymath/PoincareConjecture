




import Mathlib.Analysis.Convolution

open Set MeasureTheory ContinuousLinearMap
open scoped Topology Convolution NNReal

noncomputable section

namespace Poincare.Analysis.Convolution

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]



theorem convolution_coefficient_commutator_eq
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {q f κ : E → ℝ} (hq : Continuous q) (hf : Continuous f)
    (hκ : Continuous κ) (hκc : HasCompactSupport κ) (x : E) :
    q x * (κ ⋆[lsmul ℝ ℝ, mu] f) x -
      (κ ⋆[lsmul ℝ ℝ, mu] (fun y => q y * f y)) x =
      ∫ y, κ y * (q x - q (x - y)) * f (x - y) ∂mu := by
  have htrans : Continuous (fun y : E => x - y) := continuous_const.sub continuous_id
  have hfirst : Integrable (fun y => q x * (κ y * f (x - y))) mu :=
    ((hκ.mul (hf.comp htrans)).const_mul (q x)).integrable_of_hasCompactSupport
      (hκc.mul_right.mul_left)
  have hsecond : Integrable (fun y => κ y * (q (x - y) * f (x - y))) mu :=
    (hκ.mul ((hq.mul hf).comp htrans)).integrable_of_hasCompactSupport hκc.mul_right
  simp only [convolution_def, lsmul_apply, smul_eq_mul]
  rw [← integral_const_mul, ← integral_sub hfirst hsecond]
  apply integral_congr_ae
  filter_upwards [] with y
  ring



theorem abs_convolution_coefficient_commutator_le
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {q f κ : E → ℝ} {L : ℝ≥0} (hq : LipschitzWith L q)
    (hf : Continuous f) {B : ℝ} (hB : ∀ y, |f y| ≤ B)
    (hκ : Continuous κ) (hκc : HasCompactSupport κ) (x : E) :
    |q x * (κ ⋆[lsmul ℝ ℝ, mu] f) x -
      (κ ⋆[lsmul ℝ ℝ, mu] (fun y => q y * f y)) x| ≤
      (L : ℝ) * B * ∫ y, ‖y‖ * |κ y| ∂mu := by
  have htrans : Continuous (fun y : E => x - y) := continuous_const.sub continuous_id
  have herr : Integrable (fun y => κ y * (q x - q (x - y)) * f (x - y)) mu :=
    ((hκ.mul (continuous_const.sub (hq.continuous.comp htrans))).mul
      (hf.comp htrans)).integrable_of_hasCompactSupport (hκc.mul_right.mul_right)
  have hmajor : Integrable (fun y => (L : ℝ) * B * (‖y‖ * |κ y|)) mu :=
    ((continuous_norm.mul hκ.abs).const_mul ((L : ℝ) * B)).integrable_of_hasCompactSupport
      (hκc.abs.mul_left.mul_left)
  rw [convolution_coefficient_commutator_eq mu hq.continuous hf hκ hκc]
  calc
    |∫ y, κ y * (q x - q (x - y)) * f (x - y) ∂mu| ≤
        ∫ y, |κ y * (q x - q (x - y)) * f (x - y)| ∂mu := by
      simpa [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm
          (f := fun y => κ y * (q x - q (x - y)) * f (x - y)) (μ := mu))
    _ ≤ ∫ y, (L : ℝ) * B * (‖y‖ * |κ y|) ∂mu := by
      apply integral_mono_ae herr.norm hmajor
      filter_upwards [] with y
      have hdist : dist x (x - y) = ‖y‖ := by
        rw [dist_eq_norm]
        congr 1
        abel
      have hqdiff : |q x - q (x - y)| ≤ (L : ℝ) * ‖y‖ := by
        simpa [Real.dist_eq, hdist] using hq.dist_le_mul x (x - y)
      calc
        |κ y * (q x - q (x - y)) * f (x - y)| =
            |κ y| * |q x - q (x - y)| * |f (x - y)| := by simp [abs_mul]
        _ ≤ |κ y| * ((L : ℝ) * ‖y‖) * B :=
          mul_le_mul (mul_le_mul_of_nonneg_left hqdiff (abs_nonneg _)) (hB _)
            (abs_nonneg _) (mul_nonneg (abs_nonneg _) (mul_nonneg L.coe_nonneg (norm_nonneg _)))
        _ = (L : ℝ) * B * (‖y‖ * |κ y|) := by ring
    _ = (L : ℝ) * B * ∫ y, ‖y‖ * |κ y| ∂mu := integral_const_mul _ _

end Poincare.Analysis.Convolution
