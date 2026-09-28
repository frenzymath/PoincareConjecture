import PoincareConjecture.Proofs.M76.Rigidity.OriginalBallTopology
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.FiniteComponentExcision

set_option autoImplicit false
open Set

namespace Poincare.Topology

theorem disjoint_of_meets_old_frontier
    {X : Type*} [TopologicalSpace X] {A D R : Set X}
    (hD : IsClosed D) (hDR : D ⊆ interior R) (hA : IsPreconnected A)
    (hfront : Disjoint A (frontier D)) (hmeet : (A ∩ frontier R).Nonempty) :
    Disjoint D A := by
  rcases subset_interior_or_disjoint_of_disjoint_frontier hA hD hfront with
    hinside | houtside
  · obtain ⟨x, hxA, hxR⟩ := hmeet
    exact (hxR.2 (hDR (interior_subset (hinside hxA)))).elim
  · exact houtside.symm

end Poincare.Topology

namespace PoincareConjecture.M76.ChartwisePLBall

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {D S A R P : Set X}

theorem disjoint_of_meets_old_frontier (b : ChartwisePLBall e D S)
    (hDR : D ⊆ interior R) (hA : IsPreconnected A) (hAS : Disjoint A S)
    (hmeet : (A ∩ frontier R).Nonempty) : Disjoint D A := by
  apply Poincare.Topology.disjoint_of_meets_old_frontier b.isCompact.isClosed hDR hA
    _ hmeet
  rwa [b.frontier_eq]

theorem disjoint_of_distinct_component_meets_old_frontier
    (b : ChartwisePLBall e D S) (hDR : D ⊆ interior R)
    (hScomponent : ∀ x ∈ S, connectedComponentIn P x = S)
    (hAcomponent : ∀ x ∈ A, connectedComponentIn P x = A)
    (hne : A ≠ S) (hmeet : (A ∩ frontier R).Nonempty) : Disjoint D A := by
  obtain ⟨x, hxA, hxR⟩ := hmeet
  have hA : IsPreconnected A := by
    rw [← hAcomponent x hxA]
    exact isPreconnected_connectedComponentIn
  have hAS : Disjoint A S := by
    apply disjoint_left.mpr
    intro y hyA hyS
    exact hne ((hAcomponent y hyA).symm.trans (hScomponent y hyS))
  exact b.disjoint_of_meets_old_frontier hDR hA hAS ⟨x, hxA, hxR⟩

end PoincareConjecture.M76.ChartwisePLBall
