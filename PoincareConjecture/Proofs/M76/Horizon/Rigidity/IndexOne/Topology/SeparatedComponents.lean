import Mathlib.Topology.Connected.LocallyConnected

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76.HamiltonIntervalTorus

theorem connectedComponentIn_union_eq_of_disjoint
    {X : Type*} [TopologicalSpace X] {F G : Set X}
    [LocallyConnectedSpace F] (hF : IsClosed F) (hG : IsClosed G)
    {x : X} (hx : x ∈ F)
    (hdis : Disjoint (connectedComponentIn F x) G) :
    connectedComponentIn (F ∪ G) x = connectedComponentIn F x := by
  let S := connectedComponentIn F x
  have hSF : S ⊆ F := connectedComponentIn_subset F x
  have hpre : (Subtype.val : F → X) ⁻¹' S = connectedComponent (⟨x, hx⟩ : F) := by
    dsimp [S]
    rw [connectedComponentIn_eq_image hx,
      preimage_image_eq _ Subtype.val_injective]
  have hSc : IsClosed S := by
    dsimp [S]
    rw [connectedComponentIn_eq_image hx]
    exact hF.isClosedMap_subtype_val _ isClosed_connectedComponent
  have hSo : IsOpen ((Subtype.val : F → X) ⁻¹' S) := by
    rw [hpre]
    exact isOpen_connectedComponent
  obtain ⟨U, hU, hUS⟩ := isOpen_induced_iff.mp hSo
  have hU' : IsOpen U := hU
  have hrel : (Subtype.val : ↥(F ∪ G) → X) ⁻¹' S =
      (Subtype.val : ↥(F ∪ G) → X) ⁻¹' (U \ G) := by
    ext y
    constructor
    · intro hy
      refine ⟨?_, fun h => disjoint_left.mp hdis hy h⟩
      have h := congrArg (fun W : Set F => (⟨y, hSF hy⟩ : F) ∈ W) hUS
      exact h.mpr hy
    · rintro ⟨hyU, hyG⟩
      have hyF : (y : X) ∈ F := y.property.resolve_right hyG
      have h := congrArg (fun W : Set F => (⟨y, hyF⟩ : F) ∈ W) hUS
      exact h.mp hyU
  have hclopen : IsClopen ((Subtype.val : ↥(F ∪ G) → X) ⁻¹' S) :=
    ⟨hSc.preimage continuous_subtype_val, hrel ▸ (hU'.sdiff hG).preimage continuous_subtype_val⟩
  apply Subset.antisymm
  · rw [connectedComponentIn_eq_image (show x ∈ F ∪ G from Or.inl hx)]
    rintro y ⟨z, hz, rfl⟩
    exact hclopen.connectedComponent_subset (mem_connectedComponentIn hx) hz
  · exact connectedComponentIn_mono x subset_union_left

end PoincareConjecture.M76.HamiltonIntervalTorus
