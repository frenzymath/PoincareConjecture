import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.SourceNames.Metric
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.SourceNames.Curvature
import PoincareLib.Geometry.RicciFlow.Surgery.Control.ScheduleTheory
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.Prefix.Initial
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.Prefix.PrefixWitness
import PoincareLib.Geometry.RicciFlow.Local.Theory
import PoincareLib.Geometry.RicciFlow.Curvature.Theory
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Statement
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.DenseTheory
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.LimitTheory
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.HornTheory
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.Constants.Assembly
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.SmallNecks.ScaleBound
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.Gluing.Construction.Producer
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.InitialFlow.InitialFlow
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.InitialFlow.InitialCaptureUniqueness
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.Models.ModelAnalyticBounds
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.StandardGeometry.CapRefinement

/-!
# M45 calibrated surgery setup and initial seeds

-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

local macro "RepairedBoundedDistanceTheory" ".{" u:level "}" : term =>
  `(PoincareMT.DenseBoundedDistanceTheory.{$u})

open PoincareMT.MetricSurgery

namespace PoincareMT

/-

Natural-language theorem: given the compact M03 local-flow, M04 curvature,
M25 Appendix A, M27 kappa-solution, M28 bounded-distance, M31 singular-limit
and M32 horn-selection services, the following holds after the M34 standard-cap existence, M35
standard-cap uniqueness, M36 metric-surgery, and M44 guarded cap-persistence
providers are fixed, for every prescribed positive bound one choice of actual
standard initial metric/cap/surgery data, a fixed surgery setup with doubled
epsilon at most that bound, and positive initial seeds exist. The
source-calibration record names the threshold values, the
`C = max (Cκ) (Cstandard + 1)` choice, the canonical comparison at scale
`β * epsilon / 3`, Claim 15.1's initial-flow seed, the exact `Δ₀` minimum,
and the deep-horn selector bounds. It retains an actual Appendix A service
and a common threshold whose double is below that service's threshold,
as supplied by the M31/M32 calibration of Lemma 11.28 and Corollary 11.36.
It retains M32 selectors for every positive
analytic coefficient; the active selector can be recalibrated before any
prefix or flow is chosen. This family asserts no analytic bound on a flow.
Universal neck and round-component estimates are additional outputs, derived
from their intrinsic four-jet metric comparisons. They bound the scalar
gradient and the absolute spatial scalar-evolution expression and include
the Type-0 standard-neck application at normalized time zero. Together with
the actual kappa and standard-cap estimates they permit a model coefficient
to be selected independently of the old surgery height. They do not infer
derivative bounds from a general C-component's static geometry.
The Theorem 13.2 cutoff is at most the
actual selected metric-surgery cutoff. The returned data ties its setup to
the selected M44 cap-persistence
objects; it does not treat arbitrary numerical constants as their source.
Compatible finite prefixes are chosen afterward; no global sequence is
part of this output. M48 owns actual extension progress. M51 later applies
the initial-flow seed and constructs the global schedule. The initial capture
also supplies no surgery on [0,1/16] and curvature/full-volume estimates at
every actual time of any supplied raw flow in that interval. Ordinary
uniqueness uses its exact normalized initial metric; maximality excludes an
early surgery. Included regular domain truncations are still permitted.

Source: Morgan--Tian Definition 15.5, printed p. 359; Definitions 15.6--
15.7, printed pp. 359--360; Theorem 15.9, printed pp. 363--364; and the
inductive schedule outline, printed pp. 365--366. The selected cap/surgery
objects are the actual Proposition 16.5 data retained for later calibration;
the standard-cap canonical field and calibration are source-scale properties.
The supporting outputs explicitly include Proposition 2.19's positive
neck-scale lower bound (pp. 31--33), Proposition 15.2's two-flow gluing
at the fixed selected epsilon (pp. 353--354), and the conversion of the
standard cap to Definition 9.72 (pp. 230--231), allowing Remark 9.73's
end-coordinate reversal. One M28 threshold is retained for both the earlier-time
and dense-time bounded-distance estimates, with twice the setup accuracy below
it. The canonical constant is then selected before applying these estimates
and selecting the geometric M32 height. The supporting model estimates
use Definition 2.16 and Eq. (2.1), p. 30, Definitions 2.18 and 9.76,
pp. 31 and 231, and the spatial expression in Corollary 9.71, pp. 229--230.
Their reviewed derivation and limitations are recorded in
`reviews/contracts/2026-09-15-model-analytic-margin-round1.md`.
The actual-flow initialization, including the elementary scalar bound 18,
uses Claim 15.1, p. 353, and the discussion before Definition 15.7, p. 360;
see `reviews/contracts/2026-09-15-m45-initial-capture-round1.md`.
M27's projective-plane exception
is retained for canonical neighborhoods; its derivative estimates have no
such exception. The literal source claim of one beta for all epsilon is
stronger than the fixed-epsilon result used here and remains unresolved.
The explicit services are supplied by the checked application in
`Proofs/M45/Providers.lean`. Their geometric use and the complete conditional
derivation are reviewed in
`reviews/contracts/2026-09-18-m45-current-round1.md`. The construction below
combines the six proved producers and the supplied services. Its sharp
curvature estimate uses the closed M04 proof. The common-threshold dense export
is reviewed in `reviews/contracts/2026-09-19-m45-dense-calibration-round1.md`;
it does not itself construct the generalized histories required by M47.
-/

/-- The calibrated controlled-surgery schedules of Definitions 15.5-15.7,
pp. 359-360, assembled on the actual supplied standard and M44 objects. -/
theorem repairedControlledSchedules
    (h03 : ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [SecondCountableTopology M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [CompactSpace M], RicciFlowLocalTheory 3 M)
    (h04 : RicciFlowCurvatureTheory.{u})
    (A : RepairedNeckCapTopologyTheory.{u})
    (h27 : RepairedKappaAlternativeTheory.{u})
    (h28 : RepairedBoundedDistanceTheory.{u})
    (h31 : RepairedSingularRegularLimitTheory.{u})
    (h32 : RepairedHornSelectionTheory.{u}) :
    RepairedControlledSchedulesTheory.{u} := by
  have _ := h04
  exact M45.controlledSchedulesOfProducers A h27 h28 h31 h32
    M45.smallNeckThreshold M45.neckGluingProducer
    (M45.initialFlowProducer h03) (M45.initialCaptureProducer h03)
    M45.modelAnalyticBounds M45.capRefinementProducer

end PoincareMT
