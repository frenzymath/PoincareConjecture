import Mathlib.Topology.Constructions
import Mathlib.Topology.Maps.Basic









set_option autoImplicit false

open Set

namespace Set

variable {X : Type*} [TopologicalSpace X] {K L R S : Set X}



theorem mem_interior_subtype_preimage_iff_of_mem_interior
    (x : R) (hx : (x : X) ∈ interior R) :
    x ∈ interior ((Subtype.val : R → X) ⁻¹' L) ↔ (x : X) ∈ interior L := by
  constructor
  · intro hxrel
    obtain ⟨U, hU, hUeq⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp
      (isOpen_interior : IsOpen (interior ((Subtype.val : R → X) ⁻¹' L)))
    have hxU : (x : X) ∈ U := by
      change x ∈ (Subtype.val : R → X) ⁻¹' U
      rw [hUeq]
      exact hxrel
    have hUL : U ∩ interior R ⊆ L := by
      intro y hy
      have hyrel : (⟨y, interior_subset hy.2⟩ : R) ∈
          interior ((Subtype.val : R → X) ⁻¹' L) := by
        rw [← hUeq]
        exact hy.1
      have hyL : (⟨y, interior_subset hy.2⟩ : R) ∈
          (Subtype.val : R → X) ⁻¹' L := interior_subset hyrel
      exact hyL
    exact interior_maximal hUL (hU.inter isOpen_interior) ⟨hxU, hx⟩
  · exact fun h => preimage_interior_subset_interior_preimage continuous_subtype_val h




theorem exists_open_eq_of_relative_interior
    (hKL : K ⊆ L) (hLR : L ⊆ R) (x : R)
    (hx : x ∈ interior ((Subtype.val : R → X) ⁻¹' K)) :
    ∃ U : Set X, IsOpen U ∧ (x : X) ∈ U ∧
      ∀ y ∈ U, y ∈ L ↔ y ∈ R := by
  obtain ⟨U, hU, hUeq⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp
    (isOpen_interior : IsOpen (interior ((Subtype.val : R → X) ⁻¹' K)))
  refine ⟨U, hU, ?_, ?_⟩
  · change x ∈ (Subtype.val : R → X) ⁻¹' U
    rw [hUeq]
    exact hx
  · intro y hy
    refine ⟨fun hyL => hLR hyL, ?_⟩
    intro hyR
    have hyrel : (⟨y, hyR⟩ : R) ∈
        interior ((Subtype.val : R → X) ⁻¹' K) := by
      rw [← hUeq]
      exact hy
    have hyK : (⟨y, hyR⟩ : R) ∈
        (Subtype.val : R → X) ⁻¹' K := interior_subset hyrel
    exact hKL hyK




theorem protected_frontier_eq_of_relative_frontier
    (hR : IsClosed R) (hL : IsClosed L) (hLR : L ⊆ R)
    (hS : S ⊆ interior R)
    (hprotect : (Subtype.val : R → X) ⁻¹' frontier R ⊆
      interior ((Subtype.val : R → X) ⁻¹' L))
    (hfront : frontier ((Subtype.val : R → X) ⁻¹' L) =
      (Subtype.val : R → X) ⁻¹' S) :
    frontier L = frontier R ∪ S := by
  ext x
  constructor
  · intro hx
    have hxL : x ∈ L := hL.frontier_subset hx
    have hxR : x ∈ R := hLR hxL
    by_cases hxRi : x ∈ interior R
    · have hxrel : (⟨x, hxR⟩ : R) ∈
          frontier ((Subtype.val : R → X) ⁻¹' L) := by
        rw [(hL.preimage continuous_subtype_val).frontier_eq]
        refine ⟨hxL, ?_⟩
        intro hi
        exact hx.2 ((mem_interior_subtype_preimage_iff_of_mem_interior
          (⟨x, hxR⟩ : R) hxRi).mp hi)
      exact Or.inr (hfront.subset hxrel)
    · left
      rw [hR.frontier_eq]
      exact ⟨hxR, hxRi⟩
  · rintro (hxB | hxS)
    · have hxR : x ∈ R := hR.frontier_subset hxB
      have hxrel : (⟨x, hxR⟩ : R) ∈ (Subtype.val : R → X) ⁻¹' L :=
        interior_subset (hprotect (show (⟨x, hxR⟩ : R) ∈
          (Subtype.val : R → X) ⁻¹' frontier R from hxB))
      have hxL : x ∈ L := hxrel
      exact ⟨subset_closure hxL, fun hi => hxB.2 (interior_mono hLR hi)⟩
    · have hxR : x ∈ R := interior_subset (hS hxS)
      have hxrel : (⟨x, hxR⟩ : R) ∈
          frontier ((Subtype.val : R → X) ⁻¹' L) := by
        rw [hfront]
        exact hxS
      have hxL : x ∈ L := (hL.preimage continuous_subtype_val).frontier_subset hxrel
      exact ⟨subset_closure hxL, fun hi => hxrel.2
        (preimage_interior_subset_interior_preimage continuous_subtype_val hi)⟩

end Set
