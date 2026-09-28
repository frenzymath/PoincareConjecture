import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.Nesting



set_option autoImplicit false

open Set Metric

namespace Poincare.Manifold.Schoenflies.Reverse



theorem subset_exterior_of_isPreconnected
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (B : E ≃ₜ E) {C : Set E} (hC : IsPreconnected C)
    (havoid : Disjoint C (B '' sphere (0 : E) 1))
    (hpoint : (C ∩ (B '' closedBall (0 : E) 1)ᶜ).Nonempty) :
    C ⊆ (B '' closedBall (0 : E) 1)ᶜ := by
  apply Poincare.Topology.subset_of_isPreconnected_of_disjoint_frontier
    (B.isClosedMap _ isClosed_closedBall).isOpen_compl hC _ hpoint
  rwa [frontier_compl, ← B.image_frontier,
    frontier_closedBall (0 : E) (by norm_num : (1 : Real) ≠ 0)]

end Poincare.Manifold.Schoenflies.Reverse
