import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push

set_option autoImplicit false

open Set

namespace Poincare.Parabolic

theorem exists_point_with_doubling_bound
    {X : Type*} (S : Set X) (size radius time : X → ℝ)
    (hbounded : BddAbove (size '' S)) {L : ℝ} (hL : 0 ≤ L)
    {x : X} (hx : x ∈ S) (hxpos : 0 < size x) :
    ∃ y ∈ S, time y ≤ time x ∧ size x ≤ size y ∧
      radius y + 2 * L / size y ≤ radius x + 2 * L / size x ∧
      ∀ z ∈ S, time z ≤ time y → radius z ≤ radius y + L / size y →
        size z ≤ 2 * size y := by
  classical
  by_contra h
  push Not at h
  have hseq (k : ℕ) : ∃ y ∈ S, time y ≤ time x ∧ size x ≤ size y ∧
      radius y + 2 * L / size y ≤ radius x + 2 * L / size x ∧
      2 ^ k * size x ≤ size y := by
    induction k with
    | zero => exact ⟨x, hx, le_rfl, le_rfl, le_rfl, by simp⟩
    | succ k ih =>
      obtain ⟨y, hy, hty, hxy, hry, hqy⟩ := ih
      obtain ⟨z, hz, htz, hrz, hqz⟩ := h y hy hty hxy hry
      have hypos : 0 < size y := hxpos.trans_le hxy
      have hstep : 2 * L / size z ≤ L / size y := by
        calc
          2 * L / size z ≤ 2 * L / (2 * size y) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hqz.le
          _ = L / size y := by field_simp
      refine ⟨z, hz, htz.trans hty, hxy.trans (by linarith), ?_, ?_⟩
      · calc
          radius z + 2 * L / size z ≤ radius y + 2 * L / size y := by
            simp only [mul_div_assoc] at hstep ⊢
            linarith
          _ ≤ _ := hry
      · rw [pow_succ]
        nlinarith
  obtain ⟨K, hK⟩ := hbounded
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (K / size x) (by norm_num : (1 : ℝ) < 2)
  obtain ⟨y, hy, _, _, _, hqy⟩ := hseq k
  have hupper : size y ≤ K := hK (mem_image_of_mem size hy)
  have hlower : K < 2 ^ k * size x := (div_lt_iff₀ hxpos).mp hk
  linarith

end Poincare.Parabolic
