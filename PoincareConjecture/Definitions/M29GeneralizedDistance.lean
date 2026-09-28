import PoincareConjecture.Definitions.Ch11.BlowupLimits
import PoincareConjecture.Definitions.Ch11.SingularLimits
import PoincareConjecture.Definitions.M28BoundedDistance

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure GeneralizedBoundedDistanceHypotheses
    (S : GeneralizedBlowupSequence.{u}) (epsilon C : ℝ) where
  branch : ∀ k, generalizedPinchedOrNonnegative (S.flow k)
  canonical : ∀ k, generalizedEarlierDenseStrongCanonicalNeighborhoods
    (S.flow k) epsilon C (S.base k).1 (S.base k).2

structure GeneralizedBlowupSetup where
  sequence : GeneralizedBlowupSequence.{u}
  epsilon₀ : ℝ
  epsilon₀_pos : 0 < epsilon₀
  epsilon₀_le_one_two_hundred : epsilon₀ ≤ 1 / 200
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_le : epsilon ≤ epsilon₀
  constant : ℝ
  constant_pos : 0 < constant
  hypotheses : GeneralizedBoundedDistanceHypotheses sequence epsilon constant

end PoincareConjecture
