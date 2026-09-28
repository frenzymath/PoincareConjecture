import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Normalization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

theorem exists_smooth_disk_of_smooth_circle
    (f : sphere (0 : EuclideanSpace Real (Fin 2)) 1 -> EuclideanSpace Real (Fin 2))
    (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ f) :
    ∃ F : Diffeomorph (𝓡 2) (𝓡 2)
        (EuclideanSpace Real (Fin 2)) (EuclideanSpace Real (Fin 2)) ∞,
      F '' sphere (0 : EuclideanSpace Real (Fin 2)) 1 = range f ∧
      IsCompact (F '' closedBall (0 : EuclideanSpace Real (Fin 2)) 1) ∧
      frontier (F '' closedBall (0 : EuclideanSpace Real (Fin 2)) 1) = range f ∧
      interior (F '' closedBall (0 : EuclideanSpace Real (Fin 2)) 1) =
        F '' ball (0 : EuclideanSpace Real (Fin 2)) 1 := by
  obtain ⟨F, hF⟩ := exists_ambient_diffeomorph_of_smooth_circle f hf
  refine ⟨F, hF, (isCompact_closedBall _ _).image F.continuous, ?_, ?_⟩
  · have h := F.toHomeomorph.image_frontier (closedBall (0 : EuclideanSpace Real (Fin 2)) 1)
    rw [frontier_closedBall _ (by norm_num : (1 : Real) ≠ 0)] at h
    exact h.symm.trans hF
  · have h := F.toHomeomorph.image_interior (closedBall (0 : EuclideanSpace Real (Fin 2)) 1)
    rw [interior_closedBall _ (by norm_num : (1 : Real) ≠ 0)] at h
    exact h.symm

end Poincare.Manifold.Schoenflies
