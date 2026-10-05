import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.LocalComplementarySides

/-!
# Filling every other complementary component of a connected set

The closure of each other component meets the original connected set.
Their unions with that same set prove the literal filled complement
connected. The whole frontier remains in the original frontier.
See Wall derivation008, sections1--2 and Hamilton1976 Lemma2.
-/

set_option autoImplicit false

open Set

namespace IsClosed

variable {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
  {K : Set X}

/-- The whole frontier of an actual complementary component lies in
the original frontier. See Wall008, section1. -/
theorem frontier_connectedComponentIn_compl_subset_frontier
    (hK : IsClosed K) (x : X) :
    frontier (connectedComponentIn Kᶜ x) ⊆ frontier K := by
  have hcl : closure (connectedComponentIn Kᶜ x) ⊆ (interior K)ᶜ :=
    closure_minimal (fun _ hy hi =>
      connectedComponentIn_subset Kᶜ x hy (interior_subset hi))
      isOpen_interior.isClosed_compl
  intro y hy
  rw [hK.frontier_eq]
  exact ⟨hK.frontier_connectedComponentIn_compl_subset x hy, hcl hy.1⟩

/-- In a connected ambient space, retaining a connected closed set and
filling all but one of its complementary components gives a connected
set. The chosen component is literal. See Wall008, section2. -/
theorem isConnected_compl_connectedComponentIn [PreconnectedSpace X]
    (hK : IsClosed K) (hconn : IsConnected K) (x : X) :
    IsConnected (connectedComponentIn Kᶜ x)ᶜ := by
  let U := connectedComponentIn Kᶜ x
  have hopen : IsOpen U := hK.isOpen_compl.connectedComponentIn
  have hKU : K ⊆ Uᶜ := fun _ hy hU => connectedComponentIn_subset Kᶜ x hU hy
  obtain ⟨a, ha⟩ := hconn.nonempty
  refine ⟨⟨a, hKU ha⟩, isPreconnected_of_forall a ?_⟩
  intro y hy
  by_cases hyK : y ∈ K
  · exact ⟨K, hKU, ha, hyK, hconn.isPreconnected⟩
  · let E := connectedComponentIn Kᶜ y
    have hyE : y ∈ E := mem_connectedComponentIn hyK
    have hEU : E ⊆ Uᶜ := by
      intro z hzE hzU
      have hEq : E = U :=
        (connectedComponentIn_eq hzE).trans (connectedComponentIn_eq hzU).symm
      have hyU : y ∈ U := by
        rw [← hEq]
        exact hyE
      exact hy hyU
    have hcl : closure E ⊆ Uᶜ := closure_minimal hEU hopen.isClosed_compl
    have hproper : E ≠ univ := by
      intro he
      have haE : a ∈ E := he.symm ▸ mem_univ a
      exact connectedComponentIn_subset Kᶜ y haE ha
    obtain ⟨b, hb⟩ := nonempty_frontier_iff.mpr ⟨⟨y, hyE⟩, hproper⟩
    have hbK : b ∈ K := hK.frontier_connectedComponentIn_compl_subset y hb
    refine ⟨K ∪ closure E, union_subset hKU hcl, Or.inl ha,
      Or.inr (subset_closure hyE), ?_⟩
    exact hconn.isPreconnected.union b hbK hb.1
      isPreconnected_connectedComponentIn.closure

end IsClosed
