import PoincareConjecture.Definitions.M29GeneralizedDistance
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Generalized.BoundedDistance.DenseTheory
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Blowup.Sequence

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure DenseGeneralizedBoundedDistanceHypotheses
    (S : GeneralizedBlowupSequence.{u}) (epsilon C : ℝ) where
  branch : ∀ k, generalizedPinchedOrNonnegative (S.flow k)
  canonical : ∀ k, generalizedEarlierDenseStrongCanonicalNeighborhoods
    (S.flow k) epsilon C (S.base k).1 (S.base k).2

structure HorizonGeneralizedBlowupSetup where
  sequence : GeneralizedBlowupSequence.{u}
  epsilon₀ : ℝ
  epsilon₀_pos : 0 < epsilon₀
  epsilon₀_le_one_two_hundred : epsilon₀ ≤ 1 / 200
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_le : epsilon ≤ epsilon₀
  constant : ℝ
  constant_pos : 0 < constant
  hypotheses : DenseGeneralizedBoundedDistanceHypotheses sequence epsilon constant

end PoincareConjecture
