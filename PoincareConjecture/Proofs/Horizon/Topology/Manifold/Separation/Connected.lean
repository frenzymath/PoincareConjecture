import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Connected.Clopen











open Set Topology

namespace Poincare.Topology

variable {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
  [LocallyConnectedSpace X]

omit [ConnectedSpace X] [LocallyConnectedSpace X] in

theorem connectedComponentIn_eq_of_open_partition {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) (hdis : Disjoint A B)
    (hconn : IsPreconnected A) {x : X} (hx : x ∈ A) :
    connectedComponentIn (A ∪ B) x = A := by
  apply Subset.antisymm
  · rcases isPreconnected_connectedComponentIn.subset_or_subset hA hB hdis
      (connectedComponentIn_subset (A ∪ B) x) with h | h
    · exact h
    · exact False.elim (Set.disjoint_left.mp hdis hx
        (h (mem_connectedComponentIn (Or.inl hx))))
  · exact hconn.subset_connectedComponentIn hx subset_union_left



theorem isConnected_of_inter_of_frontier_subset {A U : Set X}
    (hA : IsOpen A) (hU : IsOpen U) (hAU : IsConnected (A ∩ U))
    (hfront : frontier A ⊆ U) (hne : A ≠ univ) : IsConnected A := by
  have hmeet (x : X) (hx : x ∈ A) :
      (connectedComponentIn A x ∩ U).Nonempty := by
    by_contra hn
    have hdis : connectedComponentIn A x ⊆ Uᶜ := by
      intro y hy hyU
      exact hn ⟨y, hy, hyU⟩
    have hclU : closure (connectedComponentIn A x) ⊆ Uᶜ :=
      closure_minimal hdis hU.isClosed_compl
    have hclA : closure (connectedComponentIn A x) ⊆ A := by
      intro y hy
      have hycl : y ∈ closure A :=
        closure_mono (connectedComponentIn_subset A x) hy
      by_contra hyA
      exact hclU hy (hfront ⟨hycl, fun hi => hyA (interior_subset hi)⟩)
    have hclosed : IsClosed (connectedComponentIn A x) := by
      apply isClosed_of_closure_subset
      exact isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
        (subset_closure (mem_connectedComponentIn hx)) hclA
    have hall : connectedComponentIn A x = univ :=
      (show IsClopen (connectedComponentIn A x) from
        ⟨hclosed, hA.connectedComponentIn⟩).eq_univ
          ⟨x, mem_connectedComponentIn hx⟩
    apply hne
    exact Set.eq_univ_of_univ_subset (hall ▸ connectedComponentIn_subset A x)
  obtain ⟨a, ha, haU⟩ := hAU.nonempty
  have hEq : connectedComponentIn A a = A := by
    apply Subset.antisymm (connectedComponentIn_subset A a)
    intro x hx
    obtain ⟨y, hy, hyU⟩ := hmeet x hx
    have hsub : A ∩ U ⊆ connectedComponentIn A y :=
      hAU.isPreconnected.subset_connectedComponentIn
        ⟨connectedComponentIn_subset A x hy, hyU⟩ inter_subset_left
    have hay : a ∈ connectedComponentIn A x := by
      rw [connectedComponentIn_eq hy]
      exact hsub ⟨ha, haU⟩
    rw [← connectedComponentIn_eq hay]
    exact mem_connectedComponentIn hx
  rw [← hEq]
  exact isConnected_connectedComponentIn_iff.mpr ha

end Poincare.Topology
