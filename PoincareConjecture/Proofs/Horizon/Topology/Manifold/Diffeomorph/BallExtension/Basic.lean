import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.BallExtension.Isotopy
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.BallExtension.Radial











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace Poincare.Manifold



theorem exists_sphere_diffeomorph_extension
    (d : Diffeomorph (𝓡 2) (𝓡 2)
      PoincareConjecture.UnitTwoSphere PoincareConjecture.UnitTwoSphere ∞) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3)
        (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)) ∞,
      F '' Metric.closedBall 0 1 = Metric.closedBall 0 1 ∧
      ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
        ∀ (p : PoincareConjecture.UnitTwoSphere) (r : ℝ),
          r ∈ Ioo (1 - δ) (1 + δ) →
            F (r • (p : EuclideanSpace ℝ (Fin 3))) =
              r • (d p : EuclideanSpace ℝ (Fin 3)) := by
  obtain ⟨A, f, hf, _, hzero, hone⟩ := exists_sphere_diffeomorph_isotopy d
  obtain ⟨F, hball, hradial⟩ :=
    exists_sphere_diffeomorph_extension_of_isotopy d A f hf hzero hone
  refine ⟨F, hball, 1 / 2, by norm_num, by norm_num, ?_⟩
  intro p r hr
  exact hradial p r (by linarith [hr.1])

end Poincare.Manifold
