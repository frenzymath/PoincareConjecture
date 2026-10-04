import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Closure

/-!
# The actual open region outside the whole protected core

Retaining the complete old frontier makes the complement of the
protected set open in the original ambient space. Relative interior
protection then puts the entire new frontier in that open region.
See Hatcher Corollary3.3, p48, and Wall derivation004, section2.
-/

set_option autoImplicit false

open Set

namespace Set

variable {X : Type*} [TopologicalSpace X] {R C K F : Set X}

/-- Removing a set which contains the entire old frontier leaves
exactly the same set as removing it from the ambient interior.
See Wall004, section2. -/
theorem sdiff_eq_interior_sdiff_of_frontier_subset
    (hBC : frontier R ⊆ C) : R \ C = interior R \ C := by
  ext x
  constructor
  · intro hx
    exact ⟨(mem_interior_iff_notMem_frontier hx.1).mpr
      (fun hf => hx.2 (hBC hf)), hx.2⟩
  · intro hx
    exact ⟨interior_subset hx.1, hx.2⟩

/-- The literal protected relative neighborhood places the complete
new frontier in the actual open avoidance region. Its intersection
with the whole ambient core frontier is exactly that new frontier.
See Wall004, section2. -/
theorem protected_open_cut_region (hC : IsClosed C)
    (hBC : frontier R ⊆ C) (hFR : F ⊆ R)
    (hprotect : (Subtype.val : R → X) ⁻¹' C ⊆
      interior ((Subtype.val : R → X) ⁻¹' K))
    (hrel : frontier ((Subtype.val : R → X) ⁻¹' K) =
      (Subtype.val : R → X) ⁻¹' F)
    (hfront : frontier K = frontier R ∪ F) :
    IsOpen (R \ C) ∧ F ⊆ R \ C ∧ (R \ C) ∩ frontier K = F := by
  have hopen : IsOpen (R \ C) := by
    rw [sdiff_eq_interior_sdiff_of_frontier_subset hBC]
    exact isOpen_interior.sdiff hC
  have hFY : F ⊆ R \ C := by
    intro x hx
    refine ⟨hFR hx, ?_⟩
    intro hxC
    have hi : (⟨x, hFR hx⟩ : R) ∈
        interior ((Subtype.val : R → X) ⁻¹' K) := hprotect hxC
    have hf : (⟨x, hFR hx⟩ : R) ∈
        frontier ((Subtype.val : R → X) ⁻¹' K) := by
      rw [hrel]
      exact hx
    exact Set.disjoint_left.mp disjoint_interior_frontier hi hf
  refine ⟨hopen, hFY, ?_⟩
  ext x
  rw [hfront]
  constructor
  · rintro ⟨hxY, hxB | hxF⟩
    · exact False.elim (hxY.2 (hBC hxB))
    · exact hxF
  · intro hxF
    exact ⟨hFY hxF, Or.inr hxF⟩

end Set
