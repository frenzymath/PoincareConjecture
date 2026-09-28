import Mathlib.Topology.Constructions

set_option autoImplicit false

open Set

theorem isOpen_union_of_closed_cover
    {X : Type*} [TopologicalSpace X] {R T A B : Set X}
    (hR : IsClosed R) (hT : IsClosed T) (hcover : R ∪ T = univ)
    (hA : A ⊆ R) (hB : B ⊆ T) (htrace : R ∩ T ⊆ A ∩ B)
    (hAo : IsOpen ((Subtype.val : R → X) ⁻¹' A))
    (hBo : IsOpen ((Subtype.val : T → X) ⁻¹' B)) :
    IsOpen (A ∪ B) := by
  have hAc := hR.isClosedMap_subtype_val _ hAo.isClosed_compl
  have hBc := hT.isClosedMap_subtype_val _ hBo.isClosed_compl
  have heq : (A ∪ B)ᶜ =
      (Subtype.val : R → X) '' ((Subtype.val : R → X) ⁻¹' A)ᶜ ∪
      (Subtype.val : T → X) '' ((Subtype.val : T → X) ⁻¹' B)ᶜ := by
    ext x
    constructor
    · intro hx
      have hxc : x ∈ R ∪ T := hcover.symm.subset (mem_univ x)
      rcases hxc with hxR | hxT
      · exact Or.inl ⟨⟨x, hxR⟩, fun h => hx (Or.inl h), rfl⟩
      · exact Or.inr ⟨⟨x, hxT⟩, fun h => hx (Or.inr h), rfl⟩
    · rintro (hx | hx)
      · rcases hx with ⟨x, hx, rfl⟩
        rintro (hxa | hxb)
        · exact hx hxa
        · exact hx (htrace ⟨x.property, hB hxb⟩).1
      · rcases hx with ⟨x, hx, rfl⟩
        rintro (hxa | hxb)
        · exact hx (htrace ⟨hA hxa, x.property⟩).2
        · exact hx hxb
  apply isClosed_compl_iff.mp
  rw [heq]
  exact hAc.union hBc
