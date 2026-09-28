import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CollarCollapse











set_option autoImplicit false

open Set

namespace CollarCollapse



noncomputable def move (r s t : ℝ) : ℝ := t - s * displacement r t



theorem move_zero (r t : ℝ) : move r 0 t = t := by
  simp only [move, zero_mul, sub_zero]



theorem move_one (r t : ℝ) : move r 1 t = height r t := by
  simp only [move, one_mul, displacement]
  ring



theorem move_add_displacement (r s t : ℝ) :
    move r s t + s * displacement r t = t := by
  simp only [move, sub_add_cancel]



theorem move_of_mem {r t : ℝ} (hr : 0 ≤ r) (ht : t ∈ Icc (-r) r) (s : ℝ) :
    move r s t = (1 - s) * t := by
  rw [move, displacement, height_of_mem hr ht]
  ring




theorem move_of_two_le_abs {r t : ℝ} (hr : 0 ≤ r) (ht : 2 * r ≤ |t|) (s : ℝ) :
    move r s t = t := by
  rw [move, displacement_eq_zero_of_two_le_abs hr ht, mul_zero, sub_zero]




theorem move_nonneg_bounds {r s t : ℝ} (hr : 0 ≤ r)
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : 0 ≤ t) :
    0 ≤ move r s t ∧ move r s t ≤ t ∧
      0 ≤ s * displacement r t ∧ s * displacement r t ≤ r := by
  obtain ⟨hh, _, hv, hvr⟩ := nonneg_bounds hr ht
  have hvt : displacement r t ≤ t := by
    dsimp only [displacement]
    linarith
  have hsv0 := mul_nonneg hs.1 hv
  have hsv := mul_le_mul_of_nonneg_right hs.2 hv
  dsimp only [move]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith




theorem move_nonpos_bounds {r s t : ℝ} (hr : 0 ≤ r)
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ≤ 0) :
    move r s t ≤ 0 ∧ t ≤ move r s t ∧
      -r ≤ s * displacement r t ∧ s * displacement r t ≤ 0 := by
  obtain ⟨hh, _, hrv, hv⟩ := nonpos_bounds hr ht
  have htv : t ≤ displacement r t := by
    dsimp only [displacement]
    linarith
  have hsv0 := mul_nonpos_of_nonneg_of_nonpos hs.1 hv
  have hsv := mul_le_mul_of_nonpos_right hs.2 hv
  dsimp only [move]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith



theorem abs_move_le {r s : ℝ} (hr : 0 ≤ r) (hs : s ∈ Icc (0 : ℝ) 1)
    (t : ℝ) : |move r s t| ≤ |t| := by
  by_cases ht : 0 ≤ t
  · obtain ⟨hh, hht, _⟩ := move_nonneg_bounds hr hs ht
    rwa [abs_of_nonneg hh, abs_of_nonneg ht]
  · have ht' : t ≤ 0 := le_of_not_ge ht
    obtain ⟨hh, hth, _⟩ := move_nonpos_bounds hr hs ht'
    rw [abs_of_nonpos hh, abs_of_nonpos ht']
    linarith



theorem abs_time_displacement_le {r s : ℝ} (hr : 0 ≤ r)
    (hs : s ∈ Icc (0 : ℝ) 1) (t : ℝ) : |s * displacement r t| ≤ r := by
  by_cases ht : 0 ≤ t
  · obtain ⟨_, _, hv, hvr⟩ := move_nonneg_bounds hr hs ht
    rwa [abs_of_nonneg hv]
  · obtain ⟨_, _, hrv, hv⟩ := move_nonpos_bounds hr hs (le_of_not_ge ht)
    rw [abs_of_nonpos hv]
    linarith



theorem move_mem_Icc {r s t delta : ℝ} (hr : 0 ≤ r)
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (-delta) delta) :
    move r s t ∈ Icc (-delta) delta := by
  exact abs_le.mp ((abs_move_le hr hs t).trans (abs_le.mpr ht))



theorem move_displacement_zero_iff {r : ℝ} (hr : 0 ≤ r) (s t : ℝ) :
    (move r s t = 0 ∧ s * displacement r t = 0) ↔ t = 0 := by
  constructor
  · rintro ⟨hm, hv⟩
    have h := move_add_displacement r s t
    rw [hm, hv, zero_add] at h
    exact h.symm
  · intro ht
    subst t
    have hh : height r 0 = 0 := height_of_mem hr ⟨by linarith, hr⟩
    simp [move, displacement, hh]



theorem continuous_move (r : ℝ) :
    Continuous (fun z : ℝ × ℝ => move r z.1 z.2) :=
  continuous_snd.sub
    (continuous_fst.mul ((continuous_displacement r).comp continuous_snd))



theorem continuous_time_displacement (r : ℝ) :
    Continuous (fun z : ℝ × ℝ => z.1 * displacement r z.2) :=
  continuous_fst.mul ((continuous_displacement r).comp continuous_snd)

end CollarCollapse
