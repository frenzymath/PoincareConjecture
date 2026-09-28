import Mathlib.Data.Finset.Card
import Mathlib.Order.Preorder.Finite

set_option autoImplicit false

namespace Finset

variable {V : Type*}

theorem exists_triangle_flag {a : Finset (Finset V)} (ha : a.Nonempty)
    (hchain : ∀ s ∈ a, ∀ u ∈ a, s ⊆ u ∨ u ⊆ s)
    {t : Finset V} (ht : t.card = 3)
    (hfaces : ∀ s ∈ a, s.Nonempty ∧ s ⊆ t) :
    ∃ p e, e ⊆ t ∧ e.card = 2 ∧ p ∈ e ∧
      ∀ s ∈ a, s = {p} ∨ s = e ∨ s = t := by
  classical
  obtain ⟨m, hm, hmin⟩ := exists_minimal ha
  have hms (s : Finset V) (hs : s ∈ a) : m ⊆ s := by
    rcases hchain m hm s hs with h | h
    · exact h
    · exact hmin hs h
  obtain ⟨p, hp⟩ := (hfaces m hm).1
  have hpt : p ∈ t := (hfaces m hm).2 hp
  have hedge : ∃ e, e ⊆ t ∧ e.card = 2 ∧ p ∈ e ∧
      ∀ s ∈ a, s.card = 2 → s = e := by
    by_cases htwo : ∃ e ∈ a, e.card = 2
    · obtain ⟨e, he, hec⟩ := htwo
      refine ⟨e, (hfaces e he).2, hec, hms e he hp, ?_⟩
      intro s hs hsc
      rcases hchain s hs e he with h | h
      · exact eq_of_subset_of_card_le h (by omega)
      · exact (eq_of_subset_of_card_le h (by omega)).symm
    · obtain ⟨e, hpe, het, hec⟩ :=
        exists_subsuperset_card_eq (singleton_subset_iff.mpr hpt)
          (show ({p} : Finset V).card ≤ 2 by simp) (show 2 ≤ t.card by omega)
      refine ⟨e, het, hec, hpe (mem_singleton_self p), ?_⟩
      intro s hs hsc
      exact (htwo ⟨s, hs, hsc⟩).elim
  obtain ⟨e, het, hec, hpe, he⟩ := hedge
  refine ⟨p, e, het, hec, hpe, ?_⟩
  intro s hs
  have hpos := (hfaces s hs).1.card_pos
  have hle := card_le_card (hfaces s hs).2
  by_cases hs1 : s.card = 1
  · exact Or.inl ((eq_of_subset_of_card_le
      (singleton_subset_iff.mpr (hms s hs hp)) (by simp [hs1])).symm)
  · by_cases hs2 : s.card = 2
    · exact Or.inr (Or.inl (he s hs hs2))
    · exact Or.inr (Or.inr (eq_of_subset_of_card_le (hfaces s hs).2 (by omega)))

end Finset
