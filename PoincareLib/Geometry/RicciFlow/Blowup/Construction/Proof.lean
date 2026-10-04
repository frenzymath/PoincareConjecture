import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Theory
import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Predecessors
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.ContractAssembly
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.ShortTime.ShortControlSupplier
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.LongTime.Assembly.LongControlSupplier

/-!
# M30 proof entry

The proof applies Morgan--Tian Theorem 11.1 (pp. 267--271) to the common
primitive controls, then Theorem 11.8 (pp. 272--279) to each finite backward
slab. Its analytic support is the
M29 bounded-distance estimate, the actual Chapter 11 generalized flow,
pointed compactness, and the curvature/noncollapse transport. Complete local
left endpoints, finite continuation, and cofinal source extraction supply
the long horizon directly from the primitive controls.
The geometric-only branch isolates the Chapter 5 extraction argument on
already supplied controlled cylinders and terminal volume, without invoking
the canonical-neighborhood derivative implication used in Lemma 11.2.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/- Natural-language theorem: for every actual varying-carrier generalized
blowup sequence, positive backward horizon, compact normalized terminal balls,
a positive normalized terminal ball-volume bound, and actual closed backward
cylinders with radius-independent slab curvature bounds and negative curvature
defect tending to zero, obtain complete geometric convergence including time
zero, with nonnegative curvature and globally bounded curvature on each compact
time slab. This supporting branch is the geometric compactness argument of
Theorem 5.11 and Proposition 5.14, pp. 89--91, with the corrected completeness
hypothesis for Theorem 5.15, pp. 91--92. It asserts no ancient noncollapse.

Given actual M04/M06/M07/M29 services, select one positive epsilon0 <= 1/400
before any sequence or geometric/analytic constant, below the actual M29 and
doubled-accuracy geometric thresholds. For every sequence with
0 < epsilon <= epsilon0, the pinched/nonnegative branch, canonical
controls on left-dense whole slices, uniform guarded scalar gradient and
absolute box-time derivative bounds, compact final balls, kappa-noncollapse, and a positive maximal
worldline-survival constant, obtain a positive-time geometric limit.
The gradient uses unit vectors of the actual metric; both analytic bounds
apply at earlier points with scalar at least four times the base scalar.
If, in addition, every finite slab below T₀
has the source's open-left-endpoint compatible embeddings and pointwise
scale-bounded noncollapse, obtain the corresponding long-horizon limit; for
T₀ = infinity it is an ancient kappa-solution on the same domain with the
limit metric and connection. Source: Morgan--Tian Theorems 11.1 and 11.8,
pp. 267--279, with Corollaries 11.3--11.4 on pp. 269--270; the finite-scale
interface records the MT-COMPACTNESS-5.15 and MT-NONCOLLAPSING-VARIANTS
errata. The nonnegative branch imposes no time normalization.
The initial partial compactness, local
splitting, Corollary 3.26 distance integration and same-map terminal jets are
internal M30 work, as derived in
`reviews/contracts/2026-09-17-m30-full-contract.md`. For the reviewed regular-time
extension, sample the original certificates on the constructed buffered compact
cylinders and transfer directly with the single doubling of Claim 11.6;
see `reviews/contracts/2026-09-18-regular-time-canonical-boundary-round1.md`. -/
/-- The controlled generalized blowup limits of Morgan--Tian Theorems 11.1
and 11.8, including terminal-time convergence and the ancient alternative. -/
theorem m30ControlledGeneralizedBlowupLimits
    (P : M30ControlledBlowupPredecessors.{u}) :
    RepairedControlledBlowupLimitTheory.{u} := by
  let services : M30.M30ContractServices.{u} := {
    mixed := M30.withinFlowJetBoundsService.{0, 0}
    flow := M30.withinBilinearFlowService.{0}
    slice := M30.spatialSliceJetConvergenceService.{0, 0, 0, 0, 0}
    short := M30.shortControlService P.m04
    long := M30.longContractService P }
  exact M30.repairedControlledBlowupLimitTheory_of_services P services

end PoincareMT
