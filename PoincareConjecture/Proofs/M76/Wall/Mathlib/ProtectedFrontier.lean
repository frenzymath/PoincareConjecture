import Mathlib.Topology.Constructions
import Mathlib.Topology.Maps.Basic

set_option autoImplicit false

open Set

namespace Set

variable {X : Type*} [TopologicalSpace X] {P R : Set X}

theorem frontier_inter_of_frontier_subset_interior
    (hP : IsClosed P) (hR : IsClosed R) (hB : frontier R ⊆ interior P) :
    frontier (P ∩ R) = frontier R ∪ (frontier P ∩ R) := by
  rw [(hP.inter hR).frontier_eq, hR.frontier_eq, hP.frontier_eq, interior_inter]
  ext x
  constructor
  · rintro ⟨⟨hxP, hxR⟩, hxnot⟩
    by_cases hxRi : x ∈ interior R
    · exact Or.inr ⟨⟨hxP, fun hxPi => hxnot ⟨hxPi, hxRi⟩⟩, hxR⟩
    · exact Or.inl ⟨hxR, hxRi⟩
  · rintro (⟨hxR, hxRi⟩ | ⟨⟨hxP, hxPi⟩, hxR⟩)
    · have hxB : x ∈ frontier R := hR.frontier_eq.symm ▸ ⟨hxR, hxRi⟩
      exact ⟨⟨interior_subset (hB hxB), hxR⟩, fun h => hxRi h.2⟩
    · exact ⟨⟨hxP, hxR⟩, fun h => hxPi h.1⟩

theorem frontier_inter_subset_interior_of_frontier_subset_interior
    (hB : frontier R ⊆ interior P) : frontier P ∩ R ⊆ interior R := by
  intro x hx
  exact (mem_interior_iff_notMem_frontier hx.2).mpr fun hxB => hx.1.2 (hB hxB)

theorem disjoint_frontier_inter_of_frontier_subset_interior
    (hB : frontier R ⊆ interior P) : Disjoint (frontier R) (frontier P ∩ R) := by
  apply disjoint_left.mpr
  intro x hxB hx
  exact hx.1.2 (hB hxB)

theorem interior_subtype_preimage_of_frontier_subset_interior
    (hB : frontier R ⊆ interior P) :
    interior ((Subtype.val : R → X) ⁻¹' P) =
      (Subtype.val : R → X) ⁻¹' interior P := by
  apply Subset.antisymm
  · intro x hx
    change (x : X) ∈ interior P
    by_contra hxPi
    have hxRi : (x : X) ∈ interior R :=
      (mem_interior_iff_notMem_frontier x.property).mpr fun hxB => hxPi (hB hxB)
    obtain ⟨U, hU, hUeq⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp
      (isOpen_interior : IsOpen (interior ((Subtype.val : R → X) ⁻¹' P)))
    have hxU : (x : X) ∈ U := by
      change x ∈ (Subtype.val : R → X) ⁻¹' U
      rw [hUeq]
      exact hx
    have hUP : U ∩ interior R ⊆ P := by
      intro y hy
      have hyR : y ∈ R := interior_subset hy.2
      have hyrel : (⟨y, hyR⟩ : R) ∈
          interior ((Subtype.val : R → X) ⁻¹' P) := by
        rw [← hUeq]
        exact hy.1
      have hyP : (⟨y, hyR⟩ : R) ∈ (Subtype.val : R → X) ⁻¹' P :=
        interior_subset hyrel
      exact hyP
    exact hxPi (interior_maximal hUP (hU.inter isOpen_interior) ⟨hxU, hxRi⟩)
  · exact preimage_interior_subset_interior_preimage continuous_subtype_val

theorem frontier_subtype_preimage_of_frontier_subset_interior
    (hP : IsClosed P) (hB : frontier R ⊆ interior P) :
    frontier ((Subtype.val : R → X) ⁻¹' P) =
      (Subtype.val : R → X) ⁻¹' frontier P := by
  rw [(hP.preimage continuous_subtype_val).frontier_eq,
    interior_subtype_preimage_of_frontier_subset_interior hB, hP.frontier_eq]
  rfl

end Set
