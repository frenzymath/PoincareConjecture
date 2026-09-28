import Mathlib.Topology.Constructions
import Mathlib.Topology.Closure









set_option autoImplicit false

open Set

namespace Set

variable {X : Type*} [TopologicalSpace X]




theorem physical_strip_cut_geometry {E C U D : Set X}
    (hE : IsClosed E) (hC : IsClosed C) (hCE : C ⊆ E)
    (hUC : U ⊆ C) (hCU : interior C ⊆ U)
    (hCdense : closure (interior C) = C)
    (hU : IsOpen ((Subtype.val : E → X) ⁻¹' U))
    (htrace : C \ U = D) :
    IsClosed (E \ U) ∧
      interior (E \ U) = interior E \ C ∧
      frontier (E \ U) = (frontier E \ U) ∪ D ∧
      C ∩ (E \ U) = D ∧ C ∪ (E \ U) = E := by
  have himage : (Subtype.val : E → X) ''
      (((Subtype.val : E → X) ⁻¹' U)ᶜ) = E \ U := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · intro hx
      exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩
  have hK : IsClosed (E \ U) := by
    rw [← himage]
    exact hE.isClosedEmbedding_subtypeVal.isClosedMap _ hU.isClosed_compl
  have hint : interior (E \ U) = interior E \ C := by
    apply Subset.antisymm
    · intro x hx
      refine ⟨interior_mono sdiff_subset hx, ?_⟩
      intro hxC
      have hxcl : x ∈ closure (interior C) := hCdense.symm ▸ hxC
      obtain ⟨y, hyK, hyC⟩ := mem_closure_iff.mp hxcl
        (interior (E \ U)) isOpen_interior hx
      exact (interior_subset hyK).2 (hCU hyC)
    · apply (isOpen_interior.sdiff hC).subset_interior_iff.mpr
      exact fun _ hx => ⟨interior_subset hx.1, fun hu => hx.2 (hUC hu)⟩
  have hfront : frontier (E \ U) = (frontier E \ U) ∪ D := by
    rw [← htrace, frontier, hK.closure_eq, hint]
    ext x
    constructor
    · intro hx
      by_cases hxi : x ∈ interior E
      · exact Or.inr ⟨by
          by_contra hxc
          exact hx.2 ⟨hxi, hxc⟩, hx.1.2⟩
      · exact Or.inl ⟨⟨subset_closure hx.1.1, hxi⟩, hx.1.2⟩
    · rintro (hx | hx)
      · exact ⟨⟨hE.frontier_subset hx.1, hx.2⟩, fun hi => hx.1.2 hi.1⟩
      · exact ⟨⟨hCE hx.1, hx.2⟩, fun hi => hi.2 hx.1⟩
  refine ⟨hK, hint, hfront, ?_, ?_⟩
  · rw [← htrace]
    ext x
    exact ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, hCE hx.1, hx.2⟩⟩
  · apply Subset.antisymm (union_subset hCE sdiff_subset)
    intro x hx
    by_cases hxU : x ∈ U
    · exact Or.inl (hUC hxU)
    · exact Or.inr ⟨hx, hxU⟩

end Set
