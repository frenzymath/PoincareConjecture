import Mathlib.Topology.Connected.LocallyConnected

/-!
# Complementary components meet every neighborhood of the separator

A complementary component is closed relative to the original complement.
If it misses an open neighborhood of the nonempty separator, it becomes
closed in the ambient space, contradicting connectedness. Its complete
ambient frontier is contained in the separator. See Brown derivation014,
sections3--4.
-/

set_option autoImplicit false

open Set

namespace BrownCollar

variable {X : Type*} [TopologicalSpace X] {S C : Set X}

/-- Relative closedness of a complementary component is expressed using
an actual ambient closed set. See Brown derivation014, section3. -/
theorem complement_component_closed_representation {x : X} (hx : x ∈ Sᶜ) :
    ∃ F : Set X, IsClosed F ∧ connectedComponentIn Sᶜ x = F ∩ Sᶜ := by
  obtain ⟨F, hF, hrep⟩ :=
    (isClosed_connectedComponent (x := (⟨x, hx⟩ : ↥(Sᶜ)))).image_val
  exact ⟨F, hF, (connectedComponentIn_eq_image hx).trans hrep⟩

/-- Every component of the original complement meets every open
neighborhood of the nonempty separator. The component itself is produced
by `connectedComponentIn`. See Brown derivation014, section3. -/
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

/-- The complete ambient frontier of each complementary component is
contained in the original closed separator. See Brown derivation014,
section4. -/
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
