import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkCofaceCount
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜]
  [AddCommGroup E] [Module 𝕜 E]

theorem ncard_surface_face_chain_extensions (K : SimplicialComplex 𝕜 E)
    (hbound : ∀ u ∈ K.faces, u.card ≤ 3)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {u : Finset E | u ∈ K.faces ∧ u.card = 3 ∧ e ⊆ u}.ncard = 2)
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hst : s ⊂ t) :
    {u : Finset E | u ∈ K.faces ∧ u ≠ s ∧ u ≠ t ∧
      (u ⊆ s ∨ s ⊆ u) ∧ (u ⊆ t ∨ t ⊆ u)}.ncard = 2 := by
  classical
  have hscpos := (K.nonempty_of_mem_faces hs).card_pos
  have hstc := Finset.card_lt_card hst
  have htcle := hbound t ht
  have hneq (u v : Finset E) (h : u ≠ v) (hc : u ⊆ v ∨ v ⊆ u) :
      u.card ≠ v.card := by
    intro heq
    rcases hc with huv | hvu
    · exact h (Finset.eq_of_subset_of_card_le huv heq.symm.le)
    · exact h (Finset.eq_of_subset_of_card_le hvu heq.le).symm
  have hranks : (s.card = 1 ∧ t.card = 2) ∨
      (s.card = 1 ∧ t.card = 3) ∨ (s.card = 2 ∧ t.card = 3) := by omega
  rcases hranks with ⟨hsc, htc⟩ | ⟨hsc, htc⟩ | ⟨hsc, htc⟩
  · have heq : {u : Finset E | u ∈ K.faces ∧ u ≠ s ∧ u ≠ t ∧
        (u ⊆ s ∨ s ⊆ u) ∧ (u ⊆ t ∨ t ⊆ u)} =
        {u : Finset E | u ∈ K.faces ∧ u.card = 3 ∧ t ⊆ u} := by
      ext u
      constructor
      · rintro ⟨hu, hus, hut, hsu, htu⟩
        have hpos := (K.nonempty_of_mem_faces hu).card_pos
        have hle := hbound u hu
        have hns := hneq u s hus hsu
        have hnt := hneq u t hut htu
        have huc : u.card = 3 := by omega
        refine ⟨hu, huc, ?_⟩
        rcases htu with h | h
        · have hh := Finset.card_le_card h
          omega
        · exact h
      · rintro ⟨hu, huc, htu⟩
        refine ⟨hu, ?_, ?_, Or.inr (hst.subset.trans htu), Or.inr htu⟩
        · intro h
          have hh := congrArg Finset.card h
          omega
        · intro h
          have hh := congrArg Finset.card h
          omega
    rw [heq]
    exact hcofaces t ht htc
  · have heq : {u : Finset E | u ∈ K.faces ∧ u ≠ s ∧ u ≠ t ∧
        (u ⊆ s ∨ s ⊆ u) ∧ (u ⊆ t ∨ t ⊆ u)} =
        ((t.powersetCard 2).filter (s ⊆ ·) : Set (Finset E)) := by
      ext u
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard]
      constructor
      · rintro ⟨hu, hus, hut, hsu, htu⟩
        have hpos := (K.nonempty_of_mem_faces hu).card_pos
        have hle := hbound u hu
        have hns := hneq u s hus hsu
        have hnt := hneq u t hut htu
        have huc : u.card = 2 := by omega
        have hut' : u ⊆ t := by
          rcases htu with h | h
          · exact h
          · have hh := Finset.card_le_card h
            omega
        have hsu' : s ⊆ u := by
          rcases hsu with h | h
          · have hh := Finset.card_le_card h
            omega
          · exact h
        exact ⟨⟨hut', huc⟩, hsu'⟩
      · rintro ⟨⟨hut, huc⟩, hsu⟩
        refine ⟨K.down_closed ht hut (Finset.card_pos.mp (by omega)),
          ?_, ?_, Or.inr hsu, Or.inl hut⟩
        · intro h
          have hh := congrArg Finset.card h
          omega
        · intro h
          have hh := congrArg Finset.card h
          omega
    rw [heq, ncard_coe_finset,
      Finset.card_filter_powersetCard_subset s t 2 hst.subset (by omega), hsc, htc]
    decide
  · have heq : {u : Finset E | u ∈ K.faces ∧ u ≠ s ∧ u ≠ t ∧
        (u ⊆ s ∨ s ⊆ u) ∧ (u ⊆ t ∨ t ⊆ u)} =
        (s.powersetCard 1 : Set (Finset E)) := by
      ext u
      simp only [Finset.mem_coe, Finset.mem_powersetCard]
      constructor
      · rintro ⟨hu, hus, hut, hsu, htu⟩
        have hpos := (K.nonempty_of_mem_faces hu).card_pos
        have hle := hbound u hu
        have hns := hneq u s hus hsu
        have hnt := hneq u t hut htu
        have huc : u.card = 1 := by omega
        refine ⟨?_, huc⟩
        rcases hsu with h | h
        · exact h
        · have hh := Finset.card_le_card h
          omega
      · rintro ⟨hus, huc⟩
        refine ⟨K.down_closed hs hus (Finset.card_pos.mp (by omega)),
          ?_, ?_, Or.inl hus, Or.inl (hus.trans hst.subset)⟩
        · intro h
          have hh := congrArg Finset.card h
          omega
        · intro h
          have hh := congrArg Finset.card h
          omega
    rw [heq, ncard_coe_finset, Finset.card_powersetCard, hsc]
    decide

end Geometry.SimplicialComplex
