import PoincareConjecture.Proofs.M38.ClosedSetNesting
import PoincareConjecture.Proofs.M38.SurgeryBallTopology
import Mathlib.Order.Preorder.Finite

set_option autoImplicit false

open Set Topology

universe u

namespace PoincareConjecture.M38

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

end PoincareConjecture.M38
