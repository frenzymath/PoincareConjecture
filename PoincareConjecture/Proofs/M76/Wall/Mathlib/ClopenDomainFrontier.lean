import Mathlib.Topology.Constructions
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Compactness.Compact











set_option autoImplicit false

open Set

namespace Set

variable {X : Type*} [TopologicalSpace X] {P L U : Set X}



theorem exists_open_inter_of_relative_open (hLP : L ⊆ P)
    (hL : IsOpen ((Subtype.val : P → X) ⁻¹' L)) :
    ∃ U : Set X, IsOpen U ∧ L = P ∩ U := by
  obtain ⟨U, hU, hUL⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hL
  refine ⟨U, hU, ?_⟩
  ext x
  constructor
  · intro hxL
    refine ⟨hLP hxL, ?_⟩
    have hx : (⟨x, hLP hxL⟩ : P) ∈ (Subtype.val : P → X) ⁻¹' L := hxL
    rw [← hUL] at hx
    exact hx
  · rintro ⟨hxP, hxU⟩
    have hx : (⟨x, hxP⟩ : P) ∈ (Subtype.val : P → X) ⁻¹' U := hxU
    rw [hUL] at hx
    exact hx



theorem interior_eq_inter_of_eq_inter_open (hU : IsOpen U) (hL : L = P ∩ U) :
    interior L = L ∩ interior P := by
  rw [hL, interior_inter, hU.interior_eq]
  ext x
  exact ⟨fun hx => ⟨⟨interior_subset hx.1, hx.2⟩, hx.1⟩,
    fun hx => ⟨hx.2, hx.1.2⟩⟩



theorem frontier_eq_inter_of_eq_inter_open (hP : IsClosed P) (hL : IsClosed L)
    (hU : IsOpen U) (hLU : L = P ∩ U) :
    frontier L = L ∩ frontier P := by
  have hLP : L ⊆ P := by
    rw [hLU]
    exact inter_subset_left
  rw [hL.frontier_eq, hP.frontier_eq,
    interior_eq_inter_of_eq_inter_open hU hLU]
  ext x
  constructor
  · rintro ⟨hxL, hxnot⟩
    exact ⟨hxL, hLP hxL, fun hxPi => hxnot ⟨hxL, hxPi⟩⟩
  · rintro ⟨hxL, _, hxnot⟩
    exact ⟨hxL, fun hx => hxnot hx.2⟩



theorem isCompact_connectedComponentIn_of_mem (hP : IsCompact P)
    {x : X} (hxP : x ∈ P) : IsCompact (connectedComponentIn P x) := by
  let : CompactSpace P := isCompact_iff_compactSpace.mp hP
  rw [connectedComponentIn_eq_image hxP]
  exact isClosed_connectedComponent.isCompact.image continuous_subtype_val



theorem isOpen_preimage_connectedComponentIn [LocallyConnectedSpace P]
    {x : X} (hxP : x ∈ P) :
    IsOpen ((Subtype.val : P → X) ⁻¹' connectedComponentIn P x) := by
  rw [connectedComponentIn_eq_image hxP,
    preimage_image_eq _ Subtype.coe_injective]
  exact isOpen_connectedComponent

end Set
