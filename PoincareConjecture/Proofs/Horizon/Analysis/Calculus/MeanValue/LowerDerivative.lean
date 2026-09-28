import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set

namespace Poincare.Analysis

lemma exists_neg_deriv_le_div {f : ℝ → ℝ} {a b C : ℝ}
    (hab : a < b) (hc : ContinuousOn f (Icc a b))
    (hd : DifferentiableOn ℝ f (Ioo a b))
    (ha : f a ≤ C) (hb : 0 ≤ f b) :
    ∃ t ∈ Ioo a b, -(deriv f t) ≤ C / (b - a) := by
  obtain ⟨t, ht, heq⟩ := exists_deriv_eq_slope f hab hc hd
  refine ⟨t, ht, ?_⟩
  rw [heq, ← neg_div]
  apply div_le_div_of_nonneg_right _ (sub_pos.mpr hab).le
  linarith

lemma exists_neg_deriv_le_of_power_bound {A : ℝ → ℝ} {b α : ℝ} {m : ℕ}
    (hb : 0 < b) (hm : 1 ≤ m)
    (hc : ContinuousOn A (Icc b (3 * b / 2)))
    (hd : DifferentiableOn ℝ A (Ioo b (3 * b / 2)))
    (hleft : A b ≤ α * b ^ m) (hright : 0 ≤ A (3 * b / 2)) :
    ∃ t ∈ Ioo b (3 * b / 2), -(deriv A t) ≤ 2 * α * b ^ (m - 1) := by
  obtain ⟨t, ht, hbound⟩ := exists_neg_deriv_le_div (by linarith : b < 3 * b / 2)
    hc hd hleft hright
  refine ⟨t, ht, hbound.trans_eq ?_⟩
  have hm' : m = (m - 1) + 1 := (Nat.sub_add_cancel hm).symm
  conv_lhs => rw [hm', pow_succ]
  field_simp
  ring

end Poincare.Analysis
