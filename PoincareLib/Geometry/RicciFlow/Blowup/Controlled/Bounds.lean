import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.DenseTheory
import PoincareLib.Geometry.RicciFlow.Blowup.Sequence

/-!
Adapted from Mapher `PoincareMT/Definitions/M29GeneralizedDistance.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# M29 generalized bounded-distance data

Morgan--Tian Theorem 11.1, pp. 267--271, first applies the bounded-distance
argument of Theorem 10.2 to each member of a generalized blowup sequence. The
sequence has changing slice carriers, so this interface uses the actual
`GeneralizedRicciFlowData` objects from Chapter 11 rather than a fixed-carrier
ancient-flow coercion or the provisional boxed-flow compatibility layer.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-! Primitive hypotheses for M28's dense-time consequence of Theorem 10.2. -/
structure DenseGeneralizedBoundedDistanceHypotheses
    (S : GeneralizedBlowupSequence.{u}) (epsilon C : ℝ) where
  branch : ∀ k, generalizedPinchedOrNonnegative (S.flow k)
  canonical : ∀ k, generalizedEarlierDenseStrongCanonicalNeighborhoods
    (S.flow k) epsilon C (S.base k).1 (S.base k).2

/-! Compatibility setup for the primitive sequence data. No current theorem
consumes this wrapper; M29's statement chooses its threshold independently
through the actual M28 service. -/
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
  hypotheses : DenseGeneralizedBoundedDistanceHypotheses sequence epsilon constant

end PoincareMT
