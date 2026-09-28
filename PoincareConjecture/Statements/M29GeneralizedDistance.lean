import PoincareConjecture.Definitions.M29GeneralizedDistance
import PoincareConjecture.Statements.M28BoundedDistance

set_option autoImplicit false

universe u

namespace PoincareConjecture

structure RepairedGeneralizedBoundedDistanceTheory : Prop where

  constants : ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
    ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
      ∀ C : ℝ, 0 < C →
        ∀ (S : GeneralizedBlowupSequence.{u}),
          GeneralizedBoundedDistanceHypotheses S epsilon C →
            GeneralizedBlowupBoundedDistance S

end PoincareConjecture
