import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

set_option autoImplicit false

open scoped intervalIntegral

namespace PoincareConjecture.Proofs.M09

theorem integral_join_error_bound (f g h : ℝ → ℝ) (a b c d C : ℝ)
    (hd : 0 < d) (hac : a ≤ c - d) (hcb : c + d ≤ b)
    (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hg : IntervalIntegrable g MeasureTheory.volume a b)
    (hh : IntervalIntegrable h MeasureTheory.volume a b)
    (hleft : Set.EqOn h f (Set.Ioo a (c - d)))
    (hright : Set.EqOn h g (Set.Ioo (c + d) b))
    (hbound : ∀ s ∈ Set.Icc (c - d) (c + d), |f s| ≤ C ∧ |g s| ≤ C ∧ |h s| ≤ C) :
    |(∫ s in a..b, h s) - ((∫ s in a..c, f s) + ∫ s in c..b, g s)| ≤ 4 * C * d := by
  have hab : a ≤ b := by linarith
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have hc : c ∈ Set.Icc a b := ⟨by linarith, by linarith⟩
  have hl : c - d ∈ Set.Icc a b := ⟨hac, by linarith⟩
  have hr : c + d ∈ Set.Icc a b := ⟨by linarith, hcb⟩
  have mono (k : ℝ → ℝ) (hk : IntervalIntegrable k MeasureTheory.volume a b)
      (x y : ℝ) (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
      IntervalIntegrable k MeasureTheory.volume x y := by
    exact hk.mono_set (Set.uIcc_subset_uIcc
      (by simpa only [Set.uIcc_of_le hab] using hx)
      (by simpa only [Set.uIcc_of_le hab] using hy))
  have hL : (∫ s in a..c - d, h s) = ∫ s in a..c - d, f s :=
    intervalIntegral.integral_congr_Ioo_of_le hac hleft
  have hR : (∫ s in c + d..b, h s) = ∫ s in c + d..b, g s :=
    intervalIntegral.integral_congr_Ioo_of_le hcb hright
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (mono h hh a c ha hc) (mono h hh c b hc hb)
  have hsplitL := intervalIntegral.integral_add_adjacent_intervals
    (mono h hh a (c - d) ha hl) (mono h hh (c - d) c hl hc)
  have hsplitR := intervalIntegral.integral_add_adjacent_intervals
    (mono h hh c (c + d) hc hr) (mono h hh (c + d) b hr hb)
  have fsplit := intervalIntegral.integral_add_adjacent_intervals
    (mono f hf a (c - d) ha hl) (mono f hf (c - d) c hl hc)
  have gsplit := intervalIntegral.integral_add_adjacent_intervals
    (mono g hg c (c + d) hc hr) (mono g hg (c + d) b hr hb)
  have heq : (∫ s in a..b, h s) - ((∫ s in a..c, f s) + ∫ s in c..b, g s) =
      (∫ s in c - d..c, h s - f s) + ∫ s in c..c + d, h s - g s := by
    rw [intervalIntegral.integral_sub (mono h hh (c - d) c hl hc) (mono f hf (c - d) c hl hc),
      intervalIntegral.integral_sub (mono h hh c (c + d) hc hr) (mono g hg c (c + d) hc hr)]
    linarith
  have hboundL : ‖∫ s in c - d..c, h s - f s‖ ≤ 2 * C * d := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := c - d) (b := c) (C := 2 * C) (f := fun s ↦ h s - f s) (by
        intro s hs
        have hs' : s ∈ Set.Ioc (c - d) c := by
          simpa only [Set.uIoc_of_le (by linarith : c - d ≤ c)] using hs
        have hm : s ∈ Set.Icc (c - d) (c + d) := ⟨hs'.1.le, by linarith [hs'.2]⟩
        simpa only [Real.norm_eq_abs] using (norm_sub_le (h s) (f s)).trans
          (by simpa only [Real.norm_eq_abs, ← two_mul] using
            add_le_add (hbound s hm).2.2 (hbound s hm).1))
    simpa only [sub_sub_cancel, abs_of_pos hd] using h
  have hboundR : ‖∫ s in c..c + d, h s - g s‖ ≤ 2 * C * d := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := c) (b := c + d) (C := 2 * C) (f := fun s ↦ h s - g s) (by
        intro s hs
        have hs' : s ∈ Set.Ioc c (c + d) := by
          simpa only [Set.uIoc_of_le (by linarith : c ≤ c + d)] using hs
        have hm : s ∈ Set.Icc (c - d) (c + d) := ⟨by linarith [hs'.1], hs'.2⟩
        simpa only [Real.norm_eq_abs] using (norm_sub_le (h s) (g s)).trans
          (by simpa only [Real.norm_eq_abs, ← two_mul] using
            add_le_add (hbound s hm).2.2 (hbound s hm).2.1))
    simpa only [add_sub_cancel_left, abs_of_pos hd] using h
  rw [heq, ← Real.norm_eq_abs]
  exact (norm_add_le _ _).trans (by linarith)

end PoincareConjecture.Proofs.M09
