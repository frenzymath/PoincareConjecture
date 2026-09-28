import Mathlib.Topology.Connected.Clopen










set_option autoImplicit false

open Set

namespace Set

variable {X ι : Type*} [TopologicalSpace X]





theorem exists_punctured_cut_partition {s₀ s₁ : Set X}
    (hs₀ : IsClosed s₀) (hs₁ : IsClosed s₁) (q : X) (hq : q ∈ s₀ ∩ s₁)
    (D : ι → Set X) (hD : ∀ i, IsPreconnected (D i \ {q}))
    (hcover : ∀ i, D i ⊆ s₀ ∪ s₁)
    (hinter : ∀ i, D i ∩ (s₀ ∩ s₁) ⊆ {q}) :
    ∃ I : Set ι,
      (∀ i ∈ I, D i ⊆ s₀ ∧ D i ∩ s₁ ⊆ {q}) ∧
      (∀ i ∉ I, D i ⊆ s₁ ∧ D i ∩ s₀ ⊆ {q}) ∧
      (((⋃ i, D i) ∩ s₀) ∪ {q}) = (⋃ i : I, D i) ∪ {q} ∧
      (((⋃ i, D i) ∩ s₁) ∪ {q}) = (⋃ i : (Iᶜ : Set ι), D i) ∪ {q} := by
  have hside (i : ι) : D i \ {q} ⊆ s₀ \ s₁ ∨ D i \ {q} ⊆ s₁ \ s₀ := by
    have hdisj : (D i \ {q}) ∩ (s₀ ∩ s₁) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      exact fun x hx => hx.1.2 (hinter i ⟨hx.1.1, hx.2⟩)
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp (hD i) s₀ s₁ hs₀ hs₁
        (sdiff_subset.trans (hcover i)) hdisj with h | h
    · exact Or.inl (fun x hx => ⟨h hx, fun hx₁ => hx.2 (hinter i ⟨hx.1, h hx, hx₁⟩)⟩)
    · exact Or.inr (fun x hx => ⟨h hx, fun hx₀ => hx.2 (hinter i ⟨hx.1, hx₀, h hx⟩)⟩)
  let I : Set ι := {i | D i \ {q} ⊆ s₀ \ s₁}
  have hleft (i : ι) (hi : i ∈ I) : D i ⊆ s₀ ∧ D i ∩ s₁ ⊆ {q} := by
    constructor
    · intro x hx
      by_cases hxq : x = q
      · exact hxq.symm ▸ hq.1
      · exact (hi ⟨hx, hxq⟩).1
    · intro x hx
      by_contra hxq
      exact (hi ⟨hx.1, hxq⟩).2 hx.2
  have hright (i : ι) (hi : i ∉ I) : D i ⊆ s₁ ∧ D i ∩ s₀ ⊆ {q} := by
    have h := (hside i).resolve_left hi
    constructor
    · intro x hx
      by_cases hxq : x = q
      · exact hxq.symm ▸ hq.2
      · exact (h ⟨hx, hxq⟩).1
    · intro x hx
      by_contra hxq
      exact (h ⟨hx.1, hxq⟩).2 hx.2
  refine ⟨I, hleft, hright, ?_, ?_⟩
  · ext x
    constructor
    · rintro (hx | hx)
      · obtain ⟨i, hxi⟩ := mem_iUnion.mp hx.1
        by_cases hi : i ∈ I
        · exact Or.inl (mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩)
        · exact Or.inr ((hright i hi).2 ⟨hxi, hx.2⟩)
      · exact Or.inr hx
    · rintro (hx | hx)
      · obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
        exact Or.inl ⟨mem_iUnion.mpr ⟨i.val, hxi⟩, (hleft i i.property).1 hxi⟩
      · exact Or.inr hx
  · ext x
    constructor
    · rintro (hx | hx)
      · obtain ⟨i, hxi⟩ := mem_iUnion.mp hx.1
        by_cases hi : i ∈ I
        · exact Or.inr ((hleft i hi).2 ⟨hxi, hx.2⟩)
        · exact Or.inl (mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩)
      · exact Or.inr hx
    · rintro (hx | hx)
      · obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
        exact Or.inl ⟨mem_iUnion.mpr ⟨i.val, hxi⟩, (hright i i.property).1 hxi⟩
      · exact Or.inr hx

end Set
