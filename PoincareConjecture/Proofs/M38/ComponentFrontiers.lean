import Mathlib.Topology.Connected.LocallyConnected

set_option autoImplicit false

open Set Topology

namespace PoincareConjecture.M38

variable {A : Type*} [TopologicalSpace A] {O : Set A} {x y : A}

theorem mem_componentIn_of_mem_closure (hx : x ∈ O) (hy : y ∈ O)
    (h : y ∈ closure (connectedComponentIn O x)) : y ∈ connectedComponentIn O x := by
  rw [connectedComponentIn_eq_image hx] at h ⊢
  have hc : (⟨y, hy⟩ : O) ∈ closure (connectedComponent (⟨x, hx⟩ : O)) := by
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
    exact h
  rw [isClosed_connectedComponent.closure_eq] at hc
  exact ⟨⟨y, hy⟩, hc, rfl⟩

theorem componentIn_closure_inter (hx : x ∈ O) :
    closure (connectedComponentIn O x) ∩ O = connectedComponentIn O x := by
  apply Set.Subset.antisymm
  · intro y hy
    exact mem_componentIn_of_mem_closure hx hy.2 hy.1
  · intro y hy
    exact ⟨subset_closure hy, connectedComponentIn_subset O x hy⟩

variable [LocallyConnectedSpace A]

theorem componentIn_frontier_subset (hO : IsOpen O) (hx : x ∈ O) :
    frontier (connectedComponentIn O x) ⊆ frontier O := by
  rw [hO.connectedComponentIn.frontier_eq, hO.frontier_eq]
  intro y hy
  exact ⟨closure_mono (connectedComponentIn_subset O x) hy.1,
    fun hyO => hy.2 (mem_componentIn_of_mem_closure hx hyO hy.1)⟩

theorem componentIn_interior_closure (hO : IsOpen O) (hx : x ∈ O)
    (hregular : interior (closure O) = O) :
    interior (closure (connectedComponentIn O x)) = connectedComponentIn O x := by
  apply Set.Subset.antisymm
  · intro y hy
    have hyO := interior_mono (closure_mono (connectedComponentIn_subset O x)) hy
    rw [hregular] at hyO
    exact mem_componentIn_of_mem_closure hx hyO (interior_subset hy)
  · exact hO.connectedComponentIn.subset_interior_iff.mpr subset_closure

theorem componentIn_frontier_closure (hO : IsOpen O) (hx : x ∈ O)
    (hregular : interior (closure O) = O) :
    frontier (closure (connectedComponentIn O x)) = frontier (connectedComponentIn O x) := by
  rw [isClosed_closure.frontier_eq, componentIn_interior_closure hO hx hregular,
    hO.connectedComponentIn.frontier_eq]

end PoincareConjecture.M38
