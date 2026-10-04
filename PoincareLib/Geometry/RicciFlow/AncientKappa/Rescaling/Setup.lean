import PoincareLib.Geometry.RicciFlow.AncientKappa.AsymptoticSoliton

/-!
# M17 source-specific blow-up sequence setup

Morgan--Tian Theorem 9.11, Section 9.2.1, pp. 183--185, starts with one
ancient kappa-solution on a fixed carrier.  For an arbitrary sequence
`tau k -> infinity`, it chooses a reduced-length minimizing point at each
scale and rescales by `tau k⁻¹`.  This module records only that input-shaped
sequence package.  Varying-carrier generalized blow-ups, bounded-distance
estimates, compactness, and the asymptotic soliton limit belong to later
milestones.

The source convention is checked against `reviews/contracts/M17-repair-contract.md`
and `reviews/errata/2026-09-13-reduced-length-source.md`: the scale `tau` is
the rescaling parameter, not a curvature-normalized scalar at the chosen
basepoint, and the full curvature norm uses the inverse metric scale.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

/-!
The wrapper retains the exact input sequence and records that its selected
reference and scale are the prescribed `reference` and `tau`.  The actual
rescaling, minimizer, and `n/2` bound are fields of the existing
`AncientRescalingSequence`, so no second weakened sequence interface is
introduced here.
-/
structure AncientBlowupSetup
    (K : AncientKappaSolution n M) (reference : M) (tau : ℕ → ℝ) where
  sequence : AncientRescalingSequence K
  reference_eq : sequence.reference = reference
  scale_eq : sequence.scale = tau

end PoincareMT
