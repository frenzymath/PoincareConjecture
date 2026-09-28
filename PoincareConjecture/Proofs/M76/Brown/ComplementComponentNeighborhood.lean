import Mathlib.Topology.Connected.LocallyConnected

set_option autoImplicit false

open Set

namespace BrownCollar

variable {X : Type*} [TopologicalSpace X] {S C : Set X}

theorem complement_component_closed_representation {x : X} (hx : x ∈ Sᶜ) :
    ∃ F : Set X, IsClosed F ∧ connectedComponentIn Sᶜ x = F ∩ Sᶜ := by
  obtain ⟨F, hF, hrep⟩ :=
    (isClosed_connectedComponent (x := (⟨x, hx⟩ : ↥(Sᶜ)))).image_val
  exact ⟨F, hF, (connectedComponentIn_eq_image hx).trans hrep⟩

theorem complement_component_meets_neighborhood [PreconnectedSpace X]
    [LocallyConnectedSpace X] (hS : IsClosed S) (hne : S.Nonempty)
    (hC : IsOpen C) (hSC : S ⊆ C) {x : X} (hx : x ∈ Sᶜ) :
    (connectedComponentIn Sᶜ x ∩ C).Nonempty := by
  classical
  by_contra hmiss
  have hout {y : X} (hy : y ∈ connectedComponentIn Sᶜ x) : y ∉ C :=
    fun hyC => hmiss ⟨y, hy, hyC⟩
  obtain ⟨F, hF, hrep⟩ := complement_component_closed_representation hx
  have heq : connectedComponentIn Sᶜ x = F ∩ Cᶜ := by
    ext y
    constructor
    · intro hy
      exact ⟨(hrep.subset hy).1, hout hy⟩
    · intro hy
      exact hrep.symm.subset ⟨hy.1, fun hyS => hy.2 (hSC hyS)⟩
  have hclosed : IsClosed (connectedComponentIn Sᶜ x) :=
    heq.symm ▸ hF.inter hC.isClosed_compl
  have hopen : IsOpen (connectedComponentIn Sᶜ x) := hS.isOpen_compl.connectedComponentIn
  have hall : connectedComponentIn Sᶜ x = univ :=
    (show IsClopen (connectedComponentIn Sᶜ x) from ⟨hclosed, hopen⟩).eq_univ
      ⟨x, mem_connectedComponentIn hx⟩
  obtain ⟨s, hs⟩ := hne
  have hsD : s ∈ connectedComponentIn Sᶜ x := hall.symm ▸ mem_univ s
  exact (connectedComponentIn_subset Sᶜ x hsD) hs

theorem frontier_complement_component_subset [LocallyConnectedSpace X]
    (hS : IsClosed S) {x : X} (hx : x ∈ Sᶜ) :
    frontier (connectedComponentIn Sᶜ x) ⊆ S := by
  obtain ⟨F, hF, hrep⟩ := complement_component_closed_representation hx
  have hopen : IsOpen (connectedComponentIn Sᶜ x) := hS.isOpen_compl.connectedComponentIn
  intro y hy
  by_contra hyS
  rw [frontier, hopen.interior_eq] at hy
  have hDF : connectedComponentIn Sᶜ x ⊆ F := fun _ h => (hrep.subset h).1
  have hyF : y ∈ F := closure_minimal hDF hF hy.1
  exact hy.2 (hrep.symm.subset ⟨hyF, hyS⟩)

end BrownCollar
