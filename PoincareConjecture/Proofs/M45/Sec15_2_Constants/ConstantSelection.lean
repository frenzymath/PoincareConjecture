import PoincareConjecture.Definitions.M45ControlledSchedules

set_option autoImplicit false

namespace PoincareConjecture.M45

theorem exists_calibration_epsilon
    (epsilon₁ epsilonPrime epsilon₁₀ common delta radiusBound prescribed : ℝ)
    (h₁ : 0 < epsilon₁) (hPrime : 0 < epsilonPrime) (h₁₀ : 0 < epsilon₁₀)
    (hcommon : 0 < common) (hdelta : 0 < delta)
    (hradius : 0 < radiusBound) (hprescribed : 0 < prescribed) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 2 ∧
      epsilon ≤ min (1 / 200 : ℝ)
        (min radiusBound (min (epsilon₁ / 2) (min (epsilonPrime / 2) epsilon₁₀))) ∧
      epsilon ≤ min (1 / 200 : ℝ) (delta / 2) ∧
      2 * epsilon ≤ epsilon₁₀ ∧ 2 * epsilon ≤ common ∧
      2 * epsilon ≤ prescribed ∧ 2 * epsilon ≤ epsilonPrime ∧
      2 * epsilon ≤ epsilon₁ := by
  let source := min (1 / 200 : ℝ)
    (min radiusBound (min (epsilon₁ / 2) (min (epsilonPrime / 2) epsilon₁₀)))
  let epsilon := min source
    (min (delta / 2) (min (epsilon₁₀ / 2) (min (common / 2) (prescribed / 2))))
  have hsource : 0 < source := by
    dsimp [source]
    exact lt_min (by norm_num)
      (lt_min hradius (lt_min (half_pos h₁) (lt_min (half_pos hPrime) h₁₀)))
  have hpositive : 0 < epsilon := by
    dsimp [epsilon]
    exact lt_min hsource (lt_min (half_pos hdelta)
      (lt_min (half_pos h₁₀) (lt_min (half_pos hcommon) (half_pos hprescribed))))
  have hb : epsilon ≤ source ∧ epsilon ≤ delta / 2 ∧ epsilon ≤ epsilon₁₀ / 2 ∧
      epsilon ≤ common / 2 ∧ epsilon ≤ prescribed / 2 := by
    simpa only [le_min_iff] using
      (show epsilon ≤ min source
        (min (delta / 2) (min (epsilon₁₀ / 2) (min (common / 2) (prescribed / 2))))
        from le_rfl)
  have hs : epsilon ≤ 1 / 200 ∧ epsilon ≤ radiusBound ∧
      epsilon ≤ epsilon₁ / 2 ∧ epsilon ≤ epsilonPrime / 2 ∧ epsilon ≤ epsilon₁₀ := by
    simpa only [source, le_min_iff] using hb.1
  exact ⟨epsilon, hpositive, by linarith [hs.1], hb.1, le_min hs.1 hb.2.1,
    by linarith [hb.2.2.1], by linarith [hb.2.2.2.1],
    by linarith [hb.2.2.2.2], by linarith [hs.2.2.2.1], by linarith [hs.2.2.1]⟩

theorem comparison_accuracy {epsilon beta : ℝ}
    (hepsilon : 0 < epsilon) (hsmall : epsilon ≤ 1 / 200)
    (hbeta : 0 < beta) (hhalf : beta < 1 / 2) :
    0 < beta * epsilon / 3 ∧ beta * epsilon / 3 ≤ 1 / 200 ∧
      beta * epsilon / 3 < 1 / 2 := by
  have hpos : 0 < beta * epsilon / 3 := div_pos (mul_pos hbeta hepsilon) (by norm_num)
  have hle : beta * epsilon / 3 ≤ epsilon := by nlinarith
  exact ⟨hpos, hle.trans hsmall, lt_of_le_of_lt (hle.trans hsmall) (by norm_num)⟩

theorem initial_cutoff_bounds {gamma delta₁₃ V D : ℝ}
    (hgamma : 0 < gamma) (hdelta : 0 < delta₁₃) (hV : 0 < V) (hD : 0 < D) :
    0 < min gamma (min delta₁₃ (min V⁻¹ D⁻¹)) ∧
      min gamma (min delta₁₃ (min V⁻¹ D⁻¹)) ≤ gamma ∧
      min gamma (min delta₁₃ (min V⁻¹ D⁻¹)) ≤ delta₁₃ ∧
      min gamma (min delta₁₃ (min V⁻¹ D⁻¹)) ≤ V⁻¹ ∧
      min gamma (min delta₁₃ (min V⁻¹ D⁻¹)) ≤ D⁻¹ := by
  refine ⟨lt_min hgamma (lt_min hdelta (lt_min (inv_pos.mpr hV) (inv_pos.mpr hD))), ?_⟩
  simpa only [le_min_iff] using
    (show min gamma (min delta₁₃ (min V⁻¹ D⁻¹)) ≤
      min gamma (min delta₁₃ (min V⁻¹ D⁻¹)) from le_rfl)

end PoincareConjecture.M45
