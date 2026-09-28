import Mathlib.Topology.Constructions
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false

open Set

variable {X : Type*} [TopologicalSpace X] [T2Space X]

theorem relative_collar_core_geometry {K N U S : Set X}
    (hK : IsCompact K) (hNK : N ⊆ K) (hUN : U ⊆ N)
    (hopen : IsOpen ((Subtype.val : K → X) ⁻¹' U))
    (hclosure : closure U = N) (hlevel : N \ U = S)
    (hfront : frontier K ⊆ U) :
    IsCompact (K \ U) ∧ interior (K \ U) = interior K \ N ∧
      frontier (K \ U) = S ∧ K \ U ⊆ interior K ∧
      N ∩ (K \ U) = S ∧ N ∪ (K \ U) = K := by
  obtain ⟨O, hO, hOU⟩ := isOpen_induced_iff.mp hopen
  have hcore : K \ U = K \ O := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1, fun hxO => hx.2 ((Set.ext_iff.mp hOU ⟨x, hx.1⟩).mp hxO)⟩
    · intro hx
      exact ⟨hx.1, fun hxU => hx.2 ((Set.ext_iff.mp hOU ⟨x, hx.1⟩).mpr hxU)⟩
  have hclosed : IsClosed (K \ U) := by
    rw [hcore]
    exact hK.isClosed.sdiff hO
  have hint : interior (K \ U) = interior K \ N := by
    rw [Set.sdiff_eq, interior_inter, interior_compl, hclosure]
    rfl
  have hcoreInt : K \ U ⊆ interior K := by
    intro x hx
    exact (mem_interior_iff_notMem_frontier hx.1).mpr (fun h => hx.2 (hfront h))
  have hNS : N ∩ (K \ U) = S := by
    rw [← hlevel]
    ext x
    exact ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, hNK hx.1, hx.2⟩⟩
  refine ⟨hK.of_isClosed_subset hclosed sdiff_subset, hint, ?_, hcoreInt, hNS, ?_⟩
  · rw [frontier, hclosed.closure_eq, hint, ← hNS]
    ext x
    constructor
    · intro hx
      have hxN : x ∈ N := by
        by_contra h
        exact hx.2 ⟨hcoreInt hx.1, h⟩
      exact ⟨hxN, hx.1⟩
    · intro hx
      exact ⟨hx.2, fun h => h.2 hx.1⟩
  · ext x
    constructor
    · exact fun hx => hx.elim (fun h => hNK h) (fun h => h.1)
    · intro hx
      by_cases hxU : x ∈ U
      · exact Or.inl (hUN hxU)
      · exact Or.inr ⟨hx, hxU⟩
