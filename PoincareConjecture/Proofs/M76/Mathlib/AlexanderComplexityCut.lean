import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

open Set

namespace Set

variable {X ι : Type*} [TopologicalSpace X]

theorem exists_connected_cut_partition {s₀ s₁ : Set X}
    (hs₀ : IsClosed s₀) (hs₁ : IsClosed s₁)
    (D : ι → Set X) (hD : ∀ i, IsPreconnected (D i))
    (hcover : ∀ i, D i ⊆ s₀ ∪ s₁)
    (hinter : ∀ i, D i ∩ (s₀ ∩ s₁) = ∅) :
    ∃ I : Set ι,
      (∀ i ∈ I, D i ⊆ s₀ ∧ Disjoint (D i) s₁) ∧
      (∀ i ∉ I, D i ⊆ s₁ ∧ Disjoint (D i) s₀) ∧
      (⋃ i, D i) ∩ s₀ = ⋃ i : I, D i ∧
      (⋃ i, D i) ∩ s₁ = ⋃ i : (Iᶜ : Set ι), D i := by
  have hside (i : ι) : D i ⊆ s₀ ∨ D i ⊆ s₁ :=
    isPreconnected_iff_subset_of_disjoint_closed.mp (hD i)
      s₀ s₁ hs₀ hs₁ (hcover i) (hinter i)
  let I : Set ι := {i | D i ⊆ s₀}
  have hleft (i : ι) (hi : i ∈ I) : D i ⊆ s₀ ∧ Disjoint (D i) s₁ := by
    refine ⟨hi, disjoint_left.mpr ?_⟩
    intro x hx hx₁
    have h : x ∈ D i ∩ (s₀ ∩ s₁) := ⟨hx, hi hx, hx₁⟩
    simp only [hinter i, mem_empty_iff_false] at h
  have hright (i : ι) (hi : i ∉ I) : D i ⊆ s₁ ∧ Disjoint (D i) s₀ := by
    have hs := (hside i).resolve_left hi
    refine ⟨hs, disjoint_left.mpr ?_⟩
    intro x hx hx₀
    have h : x ∈ D i ∩ (s₀ ∩ s₁) := ⟨hx, hx₀, hs hx⟩
    simp only [hinter i, mem_empty_iff_false] at h
  refine ⟨I, hleft, hright, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨hx, hx₀⟩
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      by_cases hi : i ∈ I
      · exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
      · exact ((disjoint_left.mp (hright i hi).2) hxi hx₀).elim
    · intro hx
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      exact ⟨mem_iUnion.mpr ⟨i.val, hxi⟩, (hleft i i.property).1 hxi⟩
  · ext x
    constructor
    · rintro ⟨hx, hx₁⟩
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      by_cases hi : i ∈ I
      · exact ((disjoint_left.mp (hleft i hi).2) hxi hx₁).elim
      · exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
    · intro hx
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      exact ⟨mem_iUnion.mpr ⟨i.val, hxi⟩, (hright i i.property).1 hxi⟩

end Set
