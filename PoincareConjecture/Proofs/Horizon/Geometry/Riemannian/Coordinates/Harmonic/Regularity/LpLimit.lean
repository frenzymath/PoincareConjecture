import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls









noncomputable section

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace PoincareConjecture.HarmonicCoordinates

private theorem tendsto_geometric_volume_root (n : ℕ) {A ρ χ : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hχ : 1 < χ) :
    Tendsto (fun k : ℕ => ((ρ / (2 : ℝ) ^ k) ^ n * A) ^
      (1 / (2 * χ ^ k))) atTop (𝓝 (1 : ℝ)) := by
  have hconstant : Tendsto (fun k : ℕ => (1 : ℝ) / χ ^ k) atTop (𝓝 0) := by
    simpa only [pow_zero] using tendsto_pow_const_div_const_pow_of_one_lt 0 hχ
  have hlinear : Tendsto (fun k : ℕ => (k : ℝ) / χ ^ k) atTop (𝓝 0) := by
    simpa only [pow_one] using tendsto_pow_const_div_const_pow_of_one_lt 1 hχ
  have hlog : Tendsto (fun k : ℕ =>
      ((n : ℝ) * Real.log ρ + Real.log A) / 2 * (1 / χ ^ k) -
        ((n : ℝ) * Real.log 2) / 2 * ((k : ℝ) / χ ^ k)) atTop (𝓝 0) := by
    simpa using (hconstant.const_mul (((n : ℝ) * Real.log ρ + Real.log A) / 2)).sub
      (hlinear.const_mul (((n : ℝ) * Real.log 2) / 2))
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hlog
  simp only [Real.exp_zero] at hexp
  apply hexp.congr'
  filter_upwards [] with k
  rw [Real.rpow_def_of_pos (mul_pos (pow_pos (div_pos hρ (by positivity)) n) hA),
    Real.log_mul (pow_ne_zero n (div_ne_zero hρ.ne' (by positivity))) hA.ne',
    Real.log_pow, Real.log_div hρ.ne' (by positivity), Real.log_pow]
  dsimp only [Function.comp_def]
  congr 1
  ring


theorem tendsto_shrinking_ball_volume_root {n : ℕ}
    (z : EuclideanSpace ℝ (Fin n)) {ρ χ : ℝ} (hρ : 0 < ρ) (hχ : 1 < χ) :
    Tendsto (fun k : ℕ =>
      (volume (Metric.ball z (ρ / (2 : ℝ) ^ k))).toReal ^
        (1 / (2 * χ ^ k))) atTop (𝓝 (1 : ℝ)) := by
  let A := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal
  have hA : 0 < A := ENNReal.toReal_pos
    (Metric.measure_ball_pos volume _ zero_lt_one).ne' measure_ball_lt_top.ne
  have hvol (k : ℕ) :
      (volume (Metric.ball z (ρ / (2 : ℝ) ^ k))).toReal =
        (ρ / (2 : ℝ) ^ k) ^ n * A := by
    rw [Measure.addHaar_ball_of_pos volume z (div_pos hρ (by positivity)),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    simp only [finrank_euclideanSpace_fin, A]
  simpa only [hvol] using tendsto_geometric_volume_root n hA hρ hχ



theorem continuousAt_abs_le_of_shrinking_eLpNorm {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {z : EuclideanSpace ℝ (Fin n)}
    (hf : ContinuousAt f z) {ρ χ B : ℝ} (hρ : 0 < ρ) (hχ : 1 < χ)
    (hfinite : ∀ k : ℕ,
      eLpNorm f (ENNReal.ofReal (2 * χ ^ k))
        (volume.restrict (Metric.ball z (ρ / (2 : ℝ) ^ k))) ≠ ⊤)
    (hbound : ∀ k : ℕ,
      (eLpNorm f (ENNReal.ofReal (2 * χ ^ k))
        (volume.restrict (Metric.ball z (ρ / (2 : ℝ) ^ k)))).toReal ≤ B) :
    |f z| ≤ B := by
  have hB : 0 ≤ B := ENNReal.toReal_nonneg.trans (hbound 0)
  by_contra hnot
  obtain ⟨c, hBc, hcf⟩ := exists_between (lt_of_not_ge hnot)
  have hc : 0 < c := hB.trans_lt hBc
  have hnear : ∀ᶠ x in 𝓝 z, c < |f x| :=
    continuousAt_const.eventually_lt hf.abs hcf
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  have hradius : Tendsto (fun k : ℕ => ρ / (2 : ℝ) ^ k) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hevent : ∀ᶠ k : ℕ in atTop,
      c * (volume (Metric.ball z (ρ / (2 : ℝ) ^ k))).toReal ^
        (1 / (2 * χ ^ k)) ≤ B := by
    filter_upwards [hradius.eventually_lt_const hr] with k hk
    have hp : 0 < 2 * χ ^ k := mul_pos (by norm_num) (pow_pos (zero_lt_one.trans hχ) _)
    have hmono : eLpNorm (fun _ : EuclideanSpace ℝ (Fin n) => c)
        (ENNReal.ofReal (2 * χ ^ k))
        (volume.restrict (Metric.ball z (ρ / (2 : ℝ) ^ k))) ≤
      eLpNorm f (ENNReal.ofReal (2 * χ ^ k))
        (volume.restrict (Metric.ball z (ρ / (2 : ℝ) ^ k))) := by
      apply eLpNorm_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      rw [Real.norm_eq_abs, abs_of_pos hc, Real.norm_eq_abs]
      exact (hball (y := x) ((Metric.mem_ball.mp hx).trans hk)).le
    have hreal := (ENNReal.toReal_mono (hfinite k) hmono).trans (hbound k)
    rw [eLpNorm_const' c (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top,
      ENNReal.toReal_mul, ← ENNReal.toReal_rpow, Measure.restrict_apply_univ,
      ENNReal.toReal_ofReal hp.le, ← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _),
      Real.norm_eq_abs, abs_of_pos hc] at hreal
    exact hreal
  have hlimit := (tendsto_shrinking_ball_volume_root z hρ hχ).const_mul c
  have hle : c ≤ B := by
    simpa only [mul_one] using le_of_tendsto hlimit hevent
  exact (not_le_of_gt hBc) hle

end PoincareConjecture.HarmonicCoordinates
