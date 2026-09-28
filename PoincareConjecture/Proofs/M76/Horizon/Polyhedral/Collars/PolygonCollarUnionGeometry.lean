import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Maps.Basic








set_option autoImplicit false

open Set

theorem IsOpen.union_image_open_complement {X : Type*} [TopologicalSpace X]
    {S : Set X} (hS : IsOpen S) {V : Set (Set.compl S)} (hV : IsOpen V) :
    IsOpen (S ∪ (Subtype.val : Set.compl S → X) '' V) := by
  have hclosed : IsClosed ((Subtype.val : Set.compl S → X) '' Vᶜ) :=
    hS.isClosed_compl.isClosedEmbedding_subtypeVal.isClosedMap _ hV.isClosed_compl
  have heq : (S ∪ (Subtype.val : Set.compl S → X) '' V)ᶜ =
      (Subtype.val : Set.compl S → X) '' Vᶜ := by
    ext x
    constructor
    · intro hx
      have hxS : x ∉ S := fun h => hx (Or.inl h)
      refine ⟨⟨x, hxS⟩, ?_, rfl⟩
      intro hxV
      exact hx (Or.inr ⟨⟨x, hxS⟩, hxV, rfl⟩)
    · rintro ⟨x, hx, rfl⟩ (hs | hv)
      · exact x.property hs
      · obtain ⟨y, hy, he⟩ := hv
        have hyx : y = x := Subtype.ext he
        exact hx (hyx ▸ hy)
  exact isClosed_compl_iff.mp (heq ▸ hclosed)
