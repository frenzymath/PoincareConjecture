import PoincareLib.Topology.Manifold.Surgery.Event.Closed.ClosedSetNesting
import PoincareLib.Topology.Manifold.Surgery.Event.Surgery.SurgeryBallTopology
import Mathlib.Order.Preorder.Finite

/-!
# An innermost ball in a finite sphere system

Each supplied smooth sphere ball has connected inside, boundary and
outside. Disjoint boundaries and a common omitted point give nesting or
disjointness. An inclusion-minimal ball therefore contains no other
boundary, on its entire closed carrier. This is the finite selection step
in the spherical-cover proof of irreducibility used in Proposition 15.3.
-/

set_option autoImplicit false

open Set Topology

universe u

namespace PoincareMT.M38

/-- Two actual sphere balls with disjoint frontiers and a common exterior
point are nested or disjoint. Their geometry supplies all connectedness
hypotheses; no classification hypothesis is used. -/
theorem sphereBalls_nested_or_disjoint
    (B C : SurgeryBallEmbedding sphereCarrier.{u})
    (hdisjoint : Disjoint (frontier B.closedBall) (frontier C.closedBall))
    (p : sphereCarrier.{u}.carrier) (hpB : p ∉ B.closedBall) (hpC : p ∉ C.closedBall) :
    Disjoint B.closedBall C.closedBall ∨
      B.closedBall ⊆ C.closedBall ∨ C.closedBall ⊆ B.closedBall :=
  closed_regions_nested_or_disjoint
    (surgeryBall_closedImage_compact B 1 (by norm_num)).isClosed
    (surgeryBall_closedImage_compact C 1 (by norm_num)).isClosed
    (surgeryBall_closedBall_connected B).isPreconnected
    (sphereBall_complement_connected B).isPreconnected
    (surgeryBall_frontier_connected C).isPreconnected hdisjoint p hpB hpC

/-- A finite nonempty system of actual sphere balls, chosen on the sides
avoiding one point, has a ball disjoint from every other cutting sphere.
This proves innermost selection, not the existence of those fillings. -/
theorem exists_innermost_sphereBall {I : Type*} [Finite I] [Nonempty I]
    (B : I → SurgeryBallEmbedding sphereCarrier.{u})
    (hdisjoint : ∀ i j, i ≠ j →
      Disjoint (frontier (B i).closedBall) (frontier (B j).closedBall))
    (p : sphereCarrier.{u}.carrier) (hp : ∀ i, p ∉ (B i).closedBall) :
    ∃ i : I, ∀ j : I, j ≠ i →
      Disjoint (B i).closedBall (frontier (B j).closedBall) := by
  obtain ⟨i, hmin⟩ := Set.Finite.exists_minimalFor
    (fun k : I => (B k).closedBall) Set.univ (Set.toFinite Set.univ) Set.univ_nonempty
  refine ⟨i, ?_⟩
  intro j hji
  have hij : i ≠ j := Ne.symm hji
  have hfront := hdisjoint i j hij
  rcases sphereBalls_nested_or_disjoint (B i) (B j) hfront p (hp i) (hp j) with
    hsep | hsub | hsub
  · exact hsep.mono_right
      (surgeryBall_closedImage_compact (B j) 1 (by norm_num)).isClosed.frontier_subset
  · have hinner := subset_interior_of_subset_of_disjoint_frontiers
      (surgeryBall_closedImage_compact (B i) 1 (by norm_num)).isClosed hsub hfront
    apply Set.disjoint_left.mpr
    intro x hx hboundary
    exact hboundary.2 (hinner hx)
  · have heq : (B i).closedBall = (B j).closedBall :=
      Set.Subset.antisymm (hmin.le_of_le (Set.mem_univ j) hsub) hsub
    obtain ⟨x, hx⟩ := (surgeryBall_frontier_connected (B i)).nonempty
    exact (Set.disjoint_left.mp hfront hx (heq ▸ hx)).elim

end PoincareMT.M38
