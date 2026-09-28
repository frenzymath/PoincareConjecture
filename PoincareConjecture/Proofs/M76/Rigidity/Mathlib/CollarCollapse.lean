import PoincareConjecture.Proofs.M76.Mathlib.PLFiberCompression

set_option autoImplicit false

open Set

namespace CollarCollapse

noncomputable def clip (r t : ℝ) : ℝ := max (-r) (min t r)

noncomputable def height (r t : ℝ) : ℝ :=
  t - 2 * clip r t + clip (2 * r) t

noncomputable def displacement (r t : ℝ) : ℝ := t - height r t

theorem clip_of_mem {r t : ℝ} (ht : t ∈ Icc (-r) r) : clip r t = t := by
  rw [clip, min_eq_left ht.2, max_eq_right ht.1]

theorem clip_of_le {r t : ℝ} (hr : 0 ≤ r) (ht : r ≤ t) : clip r t = r := by
  rw [clip, min_eq_right ht, max_eq_right (by linarith)]

theorem clip_of_le_neg {r t : ℝ} (hr : 0 ≤ r) (ht : t ≤ -r) :
    clip r t = -r := by
  rw [clip, min_eq_left (by linarith), max_eq_left ht]

theorem height_of_mem {r t : ℝ} (hr : 0 ≤ r) (ht : t ∈ Icc (-r) r) :
    height r t = 0 := by
  rw [height, clip_of_mem ht, clip_of_mem (show t ∈ Icc (-(2 * r)) (2 * r) by
    constructor <;> linarith [ht.1, ht.2])]
  ring

theorem height_of_pos_annulus {r t : ℝ} (hr : 0 ≤ r)
    (ht : t ∈ Icc r (2 * r)) : height r t = 2 * t - 2 * r := by
  rw [height, clip_of_le hr ht.1,
    clip_of_mem (show t ∈ Icc (-(2 * r)) (2 * r) by
      exact ⟨by linarith [ht.1], ht.2⟩)]
  ring

theorem height_of_neg_annulus {r t : ℝ} (hr : 0 ≤ r)
    (ht : t ∈ Icc (-(2 * r)) (-r)) : height r t = 2 * t + 2 * r := by
  rw [height, clip_of_le_neg hr ht.2,
    clip_of_mem (show t ∈ Icc (-(2 * r)) (2 * r) by
      exact ⟨ht.1, by linarith [ht.2]⟩)]
  ring

theorem height_of_two_le {r t : ℝ} (hr : 0 ≤ r) (ht : 2 * r ≤ t) :
    height r t = t := by
  rw [height, clip_of_le hr (by linarith), clip_of_le (by linarith) ht]
  ring

theorem height_of_le_neg_two {r t : ℝ} (hr : 0 ≤ r) (ht : t ≤ -(2 * r)) :
    height r t = t := by
  rw [height, clip_of_le_neg hr (by linarith), clip_of_le_neg (by linarith) ht]
  ring

theorem nonneg_bounds {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t) :
    0 ≤ height r t ∧ height r t ≤ t ∧
      0 ≤ displacement r t ∧ displacement r t ≤ r := by
  dsimp only [displacement]
  by_cases htr : t ≤ r
  · rw [height_of_mem hr ⟨by linarith, htr⟩]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · by_cases ht2r : t ≤ 2 * r
    · rw [height_of_pos_annulus hr ⟨le_of_not_ge htr, ht2r⟩]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
    · rw [height_of_two_le hr (le_of_not_ge ht2r)]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem nonpos_bounds {r t : ℝ} (hr : 0 ≤ r) (ht : t ≤ 0) :
    height r t ≤ 0 ∧ t ≤ height r t ∧
      -r ≤ displacement r t ∧ displacement r t ≤ 0 := by
  dsimp only [displacement]
  by_cases htr : -r ≤ t
  · rw [height_of_mem hr ⟨htr, by linarith⟩]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · by_cases ht2r : -(2 * r) ≤ t
    · rw [height_of_neg_annulus hr ⟨ht2r, le_of_not_ge htr⟩]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
    · rw [height_of_le_neg_two hr (le_of_not_ge ht2r)]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem abs_height_le {r : ℝ} (hr : 0 ≤ r) (t : ℝ) :
    |height r t| ≤ |t| := by
  by_cases ht : 0 ≤ t
  · obtain ⟨hh, hht, _⟩ := nonneg_bounds hr ht
    rwa [abs_of_nonneg hh, abs_of_nonneg ht]
  · have ht' : t ≤ 0 := le_of_not_ge ht
    obtain ⟨hh, hth, _⟩ := nonpos_bounds hr ht'
    rw [abs_of_nonpos hh, abs_of_nonpos ht']
    linarith

theorem abs_displacement_le {r : ℝ} (hr : 0 ≤ r) (t : ℝ) :
    |displacement r t| ≤ r := by
  by_cases ht : 0 ≤ t
  · obtain ⟨_, _, hv, hvr⟩ := nonneg_bounds hr ht
    rwa [abs_of_nonneg hv]
  · obtain ⟨_, _, hrv, hv⟩ := nonpos_bounds hr (le_of_not_ge ht)
    rw [abs_of_nonpos hv]
    linarith

theorem displacement_eq_zero_of_two_le_abs {r t : ℝ} (hr : 0 ≤ r)
    (ht : 2 * r ≤ |t|) : displacement r t = 0 := by
  rcases le_abs.mp ht with h | h
  · rw [displacement, height_of_two_le hr h, sub_self]
  · rw [displacement, height_of_le_neg_two hr (by linarith), sub_self]

theorem continuous_clip (r : ℝ) : Continuous (clip r) := by
  unfold clip
  fun_prop

theorem continuous_height (r : ℝ) : Continuous (height r) := by
  exact (continuous_id.sub (continuous_const.mul (continuous_clip r))).add
    (continuous_clip (2 * r))

theorem continuous_displacement (r : ℝ) : Continuous (displacement r) :=
  continuous_id.sub (continuous_height r)

end CollarCollapse
