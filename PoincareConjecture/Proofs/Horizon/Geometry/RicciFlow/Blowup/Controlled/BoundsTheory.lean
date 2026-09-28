import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Blowup.Controlled.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Generalized.BoundedDistance.DenseTheory

set_option autoImplicit false

universe u

namespace PoincareConjecture

structure DenseGeneralizedBoundedDistanceTheory : Prop where

  constants : ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
    ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
      ∀ C : ℝ, 0 < C →
        ∀ (S : GeneralizedBlowupSequence.{u}),
          DenseGeneralizedBoundedDistanceHypotheses S epsilon C →
            GeneralizedBlowupBoundedDistance S

end PoincareConjecture
