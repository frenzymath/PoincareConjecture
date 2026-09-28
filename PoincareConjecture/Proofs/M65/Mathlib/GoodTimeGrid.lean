import PoincareConjecture.Proofs.M65.Mathlib.EnergyIntervals

set_option autoImplicit false

open MeasureTheory Set
open scoped intervalIntegral BigOperators

namespace PoincareConjecture.M65

theorem exists_energy_good_grid {energy : ℝ → ℝ} {a b C B h : ℝ} (n : ℕ)
    (hab : a ≤ b) (hh : 0 < h) (hend : a + (n : ℝ) * h ≤ b)
    (hnonneg : ∀ t, 0 ≤ energy t)
    (hintegrable : IntervalIntegrable energy volume a b)
    (hbound : (∫ t in a..b, energy t) ≤ C) (hB : 0 < B) :
    ∃ good : Finset ℕ, good ⊆ Finset.range n ∧
      (∀ i ∈ good, ∃ s ∈ Ioo (a + (i : ℝ) * h) (a + ((i : ℝ) + 1) * h),
        energy s ≤ B) ∧
      ((Finset.range n \ good).card : ℝ) * h ≤ C / B := by
  classical
  let good := (Finset.range n).filter (fun i : ℕ =>
    ∃ s ∈ Ioo (a + (i : ℝ) * h) (a + ((i : ℝ) + 1) * h), energy s ≤ B)
  let bad := Finset.range n \ good
  have hbad_range {i : ℕ} (hi : i ∈ bad) : i < n :=
    Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1
  have hbad (i : ℕ) (hi : i ∈ bad)
      (t : ℝ) (ht : t ∈ Ioo (a + (i : ℝ) * h) (a + ((i : ℝ) + 1) * h)) :
      B < energy t := by
    by_contra hnot
    have hgood : i ∈ good :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hbad_range hi),
        t, ht, le_of_not_gt hnot⟩
    exact (Finset.mem_sdiff.mp hi).2 hgood
  have hdisjoint : (bad : Set ℕ).PairwiseDisjoint
      (fun i => Ioo (a + (i : ℝ) * h) (a + ((i : ℝ) + 1) * h)) := by
    intro i _ j _ hij
    apply Set.disjoint_left.mpr
    intro t hti htj
    rcases lt_or_gt_of_ne hij with hij | hji
    · have hcast : (i : ℝ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt hij
      have hmul := mul_le_mul_of_nonneg_right hcast hh.le
      linarith [hti.2, htj.1]
    · have hcast : (j : ℝ) + 1 ≤ i := by exact_mod_cast Nat.succ_le_of_lt hji
      have hmul := mul_le_mul_of_nonneg_right hcast hh.le
      linarith [htj.2, hti.1]
  have hsum := energy_badIntervals_sum_le (indices := bad)
    (left := fun i => a + (i : ℝ) * h) (right := fun i => a + ((i : ℝ) + 1) * h)
    hab hnonneg hintegrable hbound hB (fun _ _ => by linarith) (by
      intro i hi t ht
      have hcast : (i : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt (hbad_range hi)
      have hmul := mul_le_mul_of_nonneg_right hcast hh.le
      have hnonneg_i := mul_nonneg (Nat.cast_nonneg (α := ℝ) i) hh.le
      constructor <;> linarith [ht.1, ht.2]) hbad hdisjoint
  have hlength (i : ℕ) : a + ((i : ℝ) + 1) * h - (a + (i : ℝ) * h) = h := by ring
  simp only [hlength, Finset.sum_const, nsmul_eq_mul] at hsum
  refine ⟨good, Finset.filter_subset _ _, ?_, hsum⟩
  intro i hi
  exact (Finset.mem_filter.mp hi).2

end PoincareConjecture.M65
