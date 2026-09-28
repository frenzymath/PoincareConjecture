import Mathlib.Topology.Order.Basic
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Data.Finset.Range
import Mathlib.Tactic

set_option autoImplicit false

open Set Filter Topology

namespace StrictAnti

theorem mem_adjacent_Icc_iff {α : Type*} [LinearOrder α] {a : ℕ → α}
    (ha : StrictAnti a) {n m : ℕ} {x : α} (hx : x ∈ Icc (a (n + 1)) (a n)) :
    x ∈ Icc (a (m + 1)) (a m) ↔
      n = m ∨ (m + 1 = n ∧ x = a n) ∨ (n + 1 = m ∧ x = a (n + 1)) := by
  constructor
  · intro hm
    rcases lt_trichotomy m n with hmn | hmn | hnm
    · have hi : m + 1 = n := ha.injective
        (le_antisymm (hm.1.trans hx.2) (ha.antitone (by omega)))
      exact Or.inr (Or.inl ⟨hi, le_antisymm hx.2 (by simpa only [hi] using hm.1)⟩)
    · exact Or.inl hmn.symm
    · have hi : n + 1 = m := ha.injective
        (le_antisymm (hx.1.trans hm.2) (ha.antitone (by omega)))
      exact Or.inr (Or.inr ⟨hi, le_antisymm (by simpa only [hi] using hm.2) hx.1⟩)
  · rintro (h | ⟨h, rfl⟩ | ⟨h, rfl⟩)
    · simpa only [← h] using hx
    · subst n
      exact ⟨le_rfl, ha.antitone (Nat.le_succ m)⟩
    · subst m
      exact ⟨ha.antitone (Nat.le_succ (n + 1)), le_rfl⟩

theorem iUnion_adjacent_Icc {α : Type*} [LinearOrder α] {a : ℕ → α}
    (ha : StrictAnti a) (N : ℕ) :
    (⋃ i ∈ Finset.range (N + 1), Icc (a (i + 1)) (a i)) = Icc (a (N + 1)) (a 0) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hsplit : (⋃ i ∈ Finset.range (N + 1 + 1), Icc (a (i + 1)) (a i)) =
        Icc (a (N + 1 + 1)) (a (N + 1)) ∪
          ⋃ i ∈ Finset.range (N + 1), Icc (a (i + 1)) (a i) := by
      ext x
      simp only [mem_iUnion, Finset.mem_range, mem_union]
      constructor
      · rintro ⟨i, hi, hx⟩
        by_cases he : i = N + 1
        · exact Or.inl (he ▸ hx)
        · exact Or.inr ⟨i, by omega, hx⟩
      · rintro (hx | ⟨i, hi, hx⟩)
        · exact ⟨N + 1, by omega, hx⟩
        · exact ⟨i, by omega, hx⟩
    rw [hsplit, ih]
    exact Icc_union_Icc_eq_Icc (ha.antitone (Nat.le_succ _))
      (ha.antitone (Nat.zero_le _))

theorem iUnion_adjacent_Icc_eq_Ioc {a : ℕ → ℝ} {c : ℝ}
    (ha : StrictAnti a) (hc : ∀ n, c < a n) (hlim : Tendsto a atTop (𝓝 c)) :
    (⋃ n, Icc (a (n + 1)) (a n)) = Ioc c (a 0) := by
  ext x
  constructor
  · rintro hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact ⟨(hc (n + 1)).trans_le hn.1, hn.2.trans (ha.antitone (Nat.zero_le n))⟩
  · intro hx
    have hevent := hlim.eventually (isOpen_Iio.mem_nhds hx.1)
    obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
    have hmem : x ∈ Icc (a (N + 1)) (a 0) :=
      ⟨(hN (N + 1) (Nat.le_succ N)).le, hx.2⟩
    rw [← ha.iUnion_adjacent_Icc N] at hmem
    simp only [mem_iUnion] at hmem
    obtain ⟨n, _, hn⟩ := hmem
    exact mem_iUnion.mpr ⟨n, hn⟩

end StrictAnti
