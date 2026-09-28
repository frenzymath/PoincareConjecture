import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.Nesting



noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E3 := EuclideanSpace Real (Fin 3)



theorem closedBall_image_subset_openBall_of_disjoint_boundaries
    (A B : E3 ≃ₜ E3)
    (hdisj : Disjoint (A '' sphere (0 : E3) 1) (B '' sphere (0 : E3) 1))
    {p : E3} (hpA : p ∈ A '' sphere (0 : E3) 1) (hpB : p ∈ B '' ball (0 : E3) 1) :
    A '' closedBall (0 : E3) 1 ⊆ B '' ball (0 : E3) 1 := by
  have hconn : IsPreconnected (A '' sphere (0 : E3) 1) :=
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num [E3])
      (0 : E3) zero_le_one).isPreconnected.image A A.continuous.continuousOn
  have hfront : frontier (B '' ball (0 : E3) 1) = B '' sphere (0 : E3) 1 := by
    rw [← B.image_frontier, frontier_ball _ one_ne_zero]
  have hboundary : A '' sphere (0 : E3) 1 ⊆ B '' ball (0 : E3) 1 := by
    apply Poincare.Topology.subset_of_isPreconnected_of_disjoint_frontier
      (B.isOpenMap _ isOpen_ball) hconn
    · rwa [hfront]
    · exact ⟨p, hpA, hpB⟩
  exact B.image_closedBall_subset_image_ball_of_sphere_subset A
    (by rw [← Module.finrank_eq_rank]; norm_num [E3]) hboundary



theorem disjoint_closedBall_images_of_exterior_boundary_points
    (A B : E3 ≃ₜ E3)
    (hdisj : Disjoint (A '' sphere (0 : E3) 1) (B '' sphere (0 : E3) 1))
    {p q : E3} (hpA : p ∈ A '' sphere (0 : E3) 1)
    (hpB : p ∉ B '' closedBall (0 : E3) 1)
    (hqB : q ∈ B '' sphere (0 : E3) 1)
    (hqA : q ∉ A '' closedBall (0 : E3) 1) :
    Disjoint (A '' closedBall (0 : E3) 1) (B '' closedBall (0 : E3) 1) := by
  rcases A.disjoint_or_nested_image_closedBall B
    (by rw [← Module.finrank_eq_rank]; norm_num [E3]) hdisj with hd | hAB | hBA
  · exact hd
  · exact (hpB (image_mono ball_subset_closedBall
      (hAB (image_mono sphere_subset_closedBall hpA)))).elim
  · exact (hqA (image_mono ball_subset_closedBall
      (hBA (image_mono sphere_subset_closedBall hqB)))).elim

end Poincare.Manifold.Schoenflies
