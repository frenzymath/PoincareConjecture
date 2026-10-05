import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Regions.OriginalBallTopology
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.FiniteComponentExcision

/-!
# Interior sphere fillings avoid the marked annulus

A connected carrier avoiding the entire frontier of a closed region is
either inside or outside. Meeting the old boundary rules out the inside
alternative for a ball contained in the old interior. Distinct whole
components of a phase supply the required frontier disjointness directly.
-/

set_option autoImplicit false
open Set

namespace Poincare.Topology

/-- A connected carrier meeting the old boundary and avoiding the frontier
of a closed interior region misses the entire region. -/
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

namespace PoincareMT.M76.ChartwisePLBall

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {D S A R P : Set X}

/-- An interior PL ball misses every connected marked carrier that avoids
its whole marked sphere and meets the original boundary. -/
theorem disjoint_of_meets_old_frontier (b : ChartwisePLBall e D S)
    (hDR : D ⊆ interior R) (hA : IsPreconnected A) (hAS : Disjoint A S)
    (hmeet : (A ∩ frontier R).Nonempty) : Disjoint D A := by
  apply Poincare.Topology.disjoint_of_meets_old_frontier b.isCompact.isClosed hDR hA
    _ hmeet
  rwa [b.frontier_eq]

/-- A ball filling one whole component of a phase cannot contain any
different whole component which meets the old boundary. In particular this
preserves the distinguished annulus and all its original rim marks. -/
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

end PoincareMT.M76.ChartwisePLBall
