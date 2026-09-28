import PoincareConjecture.Proofs.M38.FiniteSphereNesting










set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38



theorem closed_regions_disjoint_of_mutual_frontier_avoidance
    {X : Type*} [TopologicalSpace X] {B C : Set X}
    (hB : IsClosed B) (hC : IsClosed C) (hconnected : IsPreconnected B)
    (hboundary : (frontier B).Nonempty)
    (hBC : Disjoint B (frontier C)) (hCB : Disjoint C (frontier B)) :
    Disjoint B C := by
  rcases preconnected_subset_interior_or_compl hC hconnected hBC with hinner | houter
  · obtain ⟨x, hx⟩ := hboundary
    exact (Set.disjoint_left.mp hCB
      (interior_subset (hinner (hB.frontier_subset hx))) hx).elim
  · exact Set.disjoint_left.mpr (fun _ hx hy => houter hx hy)




theorem sphereBall_disjoint_translate_of_innermost
    (B : SurgeryBallEmbedding sphereCarrier.{u})
    (e : Diffeomorph (𝓡 3) (𝓡 3) sphereCarrier.{u}.carrier sphereCarrier.{u}.carrier ∞)
    (hforward : Disjoint B.closedBall (e '' frontier B.closedBall))
    (hbackward : Disjoint B.closedBall (e.symm '' frontier B.closedBall)) :
    Disjoint B.closedBall (e '' B.closedBall) := by
  have hB : IsClosed B.closedBall :=
    (surgeryBall_closedImage_compact B 1 (by norm_num)).isClosed
  have hC : IsClosed (e '' B.closedBall) := e.toHomeomorph.isClosedMap _ hB
  have hBC : Disjoint B.closedBall (frontier (e '' B.closedBall)) := by
    change Disjoint B.closedBall (frontier (e.toHomeomorph '' B.closedBall))
    rw [← e.toHomeomorph.image_frontier]
    exact hforward
  have hCB : Disjoint (e '' B.closedBall) (frontier B.closedBall) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ hboundary
    exact Set.disjoint_left.mp hbackward hx ⟨e x, hboundary, e.symm_apply_apply x⟩
  exact closed_regions_disjoint_of_mutual_frontier_avoidance hB hC
    (surgeryBall_closedBall_connected B).isPreconnected
    (surgeryBall_frontier_connected B).nonempty hBC hCB

end PoincareConjecture.M38
