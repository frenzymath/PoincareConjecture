import PoincareConjecture.Definitions.M28BoundedDistance
import PoincareConjecture.Statements.M28BoundedDistance
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Generalized.CanonicalNeighborhood



















set_option autoImplicit false

open Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure HorizonRepairedBoundedDistanceTheory : Prop where
  constants : ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
    ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
    ∀ C : ℝ, 0 < C → ∀ A : ℝ, 0 ≤ A →
      ∃ D₀ D : ℝ, 0 < D₀ ∧ 0 < D ∧
        ∀ F : GeneralizedRicciFlowData.{u},
          F.interval ⊆ Set.Ici 0 →
          generalizedHamiltonIveyPinched F →
          ∀ t, t ∈ F.interval → ∀ x : (F.slice t).carrier,
            D₀ ≤ F.scalar ⟨t, x⟩ →
            generalizedEarlierStrongCanonicalNeighborhoods F epsilon C t x →
            RepairedBoundedDistanceEstimate F A D t x

end PoincareConjecture
