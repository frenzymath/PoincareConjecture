import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Constructions
import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false

open Set

namespace PoincareConjecture.M32

theorem frontier_connectedComponentIn_subset_of_isOpen
    {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    {A : Set X} (hA : IsOpen A) (x : X) :
    frontier (connectedComponentIn A x) ⊆ frontier A := by
  by_cases hx : x ∈ A
  · have hC : IsOpen (connectedComponentIn A x) := hA.connectedComponentIn
    rw [hC.frontier_eq, hA.frontier_eq]
    intro y hy
    refine ⟨closure_mono (connectedComponentIn_subset A x) hy.1, ?_⟩
    intro hyA
    apply hy.2
    have hycl : y ∈ closure
        (Subtype.val '' connectedComponent (⟨x, hx⟩ : A)) := by
      simpa only [connectedComponentIn_eq_image hx] using hy.1
    have hyrel : (⟨y, hyA⟩ : A) ∈ closure (connectedComponent (⟨x, hx⟩ : A)) :=
      closure_subtype.mpr hycl
    rw [isClosed_connectedComponent.closure_eq] at hyrel
    rw [connectedComponentIn_eq_image hx]
    exact ⟨⟨y, hyA⟩, hyrel, rfl⟩
  · rw [connectedComponentIn_eq_empty hx]
    simp only [frontier_empty, empty_subset]

theorem exists_connectedComponentIn_mem_not_mem_of_no_filling
    {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X] [T2Space X]
    {S U K : Set X} (hS : IsClosed S)
    (hfill : ∀ K₀ : Set X, K₀ ⊆ U → (interior K₀).Nonempty →
      frontier K₀ ⊆ S → ¬ IsCompact K₀)
    (hK : IsCompact K) (hKU : K ⊆ U) {x : X} (hx : x ∉ S) :
    ∃ y ∈ connectedComponentIn Sᶜ x, y ∉ K := by
  classical
  by_contra hnone
  let C := connectedComponentIn Sᶜ x
  have hCK : C ⊆ K := by
    intro y hy
    by_contra hyK
    exact hnone ⟨y, hy, hyK⟩
  have hclosure : closure C ⊆ K := closure_minimal hCK hK.isClosed
  have hcompact : IsCompact (closure C) :=
    hK.of_isClosed_subset isClosed_closure hclosure
  have hC : IsOpen C := hS.isOpen_compl.connectedComponentIn
  have hxC : x ∈ C := mem_connectedComponentIn hx
  have hinterior : (interior (closure C)).Nonempty :=
    ⟨x, interior_maximal subset_closure hC hxC⟩
  have hfrontier : frontier C ⊆ S := by
    have h := frontier_connectedComponentIn_subset_of_isOpen hS.isOpen_compl x
    rw [frontier_compl] at h
    exact h.trans hS.frontier_subset
  exact hfill (closure C) (hclosure.trans hKU) hinterior
    (frontier_closure_subset.trans hfrontier) hcompact

end PoincareConjecture.M32
