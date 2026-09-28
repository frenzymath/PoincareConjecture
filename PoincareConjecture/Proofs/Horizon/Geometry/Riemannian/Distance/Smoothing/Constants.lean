import Mathlib.Analysis.SpecialFunctions.Sqrt



set_option autoImplicit false

namespace PoincareConjecture.RiemannianMetric



theorem exists_distance_smoothing_parameter {H eta : ℝ} (hH : 0 ≤ H) (heta : 0 < eta) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 / 4 ∧
      Real.sqrt (1 + t) / Real.sqrt (1 - t) ≤ 1 + eta ∧
      (((H + t) * (1 + t) + (1 + t) * t) + Real.sqrt (1 + t) * t) /
        (1 - t) ≤ H + eta := by
  let t := min (1 / 4) (eta / (4 * H + 10))
  have hden : 0 < 4 * H + 10 := by linarith
  have ht : 0 < t := lt_min (by norm_num) (div_pos heta hden)
  have htquarter : t ≤ 1 / 4 := min_le_left _ _
  have hscale : (4 * H + 10) * t ≤ eta := by
    have h := (le_div_iff₀ hden).mp (min_le_right (1 / 4) (eta / (4 * H + 10)))
    simpa only [t, mul_comm] using h
  have hb : 0 < 1 - t := by linarith
  have hA : 0 ≤ 1 + t := by linarith
  have hsqrtA : Real.sqrt (1 + t) ≤ 1 + t := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨hA, by nlinarith [sq_nonneg t]⟩
  have hsqrtb : 1 - t ≤ Real.sqrt (1 - t) := by
    nlinarith [Real.sq_sqrt hb.le, Real.sqrt_nonneg (1 - t)]
  have hHt : 0 ≤ H * t := mul_nonneg hH ht.le
  have hetat := mul_nonneg heta.le (sub_nonneg.mpr htquarter)
  have htt := mul_nonneg ht.le (sub_nonneg.mpr htquarter)
  refine ⟨t, ht, htquarter, ?_, ?_⟩
  · apply (div_le_iff₀ (Real.sqrt_pos.mpr hb)).mpr
    have h := mul_le_mul_of_nonneg_left hsqrtb (by linarith : 0 ≤ 1 + eta)
    nlinarith
  · apply (div_le_iff₀ hb).mpr
    have hsqrtAt := mul_le_mul_of_nonneg_right hsqrtA ht.le
    nlinarith

end PoincareConjecture.RiemannianMetric
