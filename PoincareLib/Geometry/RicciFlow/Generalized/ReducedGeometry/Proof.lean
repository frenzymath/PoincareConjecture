import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Theory
import PoincareLib.Geometry.RicciFlow.Generalized.Gauge.Geometry
import PoincareLib.Geometry.RicciFlow.Rescaling.Theory
import PoincareLib.Geometry.RicciFlow.Curvature.Theory
import PoincareLib.Geometry.RicciFlow.Curvature.Construction
import PoincareLib.Geometry.RicciFlow.Rescaling.Generalized
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Predecessors
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Assembly
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SmallTime.Stability.SmallTimeCoverage

/-!
# M14 generalized L-geometry theorem

The theorem below assembles the actual generalized path calculus,
exponential family, reduced-volume transport and analytic rescaling.
Compact small-time stability is proved by confinement and finite-energy
comparison. All coordinate services are supplied by the closed lower milestones.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology intervalIntegral BigOperators

universe u

namespace PoincareMT

variable {n : ℕ}

/--
Morgan--Tian, Chapter 6, Definitions 6.1--6.25 and Theorems 6.50--6.79
(pp. 105--147), together with Chapter 7, Definition 7.1, Proposition 7.5
and Theorems 7.10--7.26 (pp. 149--167),
and Theorem 8.1 (pp. 169--171):
for an actual generalized Ricci-flow spacetime with its horizontal
Levi-Civita calculus, backward paths use the clock equation and horizontal
projection, the square-root Euler/Jacobi and first/second variation formulas
hold on their genuine domains. Reduced length is a function of the actual
endpoint, whose clock fixes elapsed time; its backward derivative is minus
the derivative along the time vector. Positive-start formulas retain their
actual start time and endpoint derivative. The zero-start exponential family
fixes the initial tangent and asserts smoothness only on its existence domain.
Its positive-time action is jointly smooth, with initial-vector derivative
g(A,d_Z gamma), where A is the actual square-root velocity. The second
variation and Jacobi IVP require a regular Euler path; index nonnegativity
and its fixed-endpoint kernel additionally require minimality.
Fixed-time stable sets select the actual uniquely minimizing branches and
have the strict-prefix property. Calibrated Jacobian/reduced-volume transport
holds on the relative-interior regular domain, with Gaussian domination and
integrability on the displayed stable image. Whenever a complete,
bounded-curvature ordinary presentation is supplied, the same carrier yields
the M08 L-geodesic, M09 reduced-length, and M10 reduced-volume outputs through
their explicit providers. The ordinary flow has the actual cylinder metric;
capture and time-window hypotheses restrict action, regular-locus and volume
comparisons. On interior times its captured stable image has full measure,
and the actual cylinder preserves measure on every measurable captured subset.
Ordinary providers are required only for this branch. Attainment identifies
the action of an actual stable minimizing branch with the infimum; finite
action alone is never asserted to produce a minimizer on a generalized flow.
With one full-curvature bound on a valid past slab, every compact initial-vector
set is stable for sufficiently small positive times, and its short branches
stay in a supplied compact neighborhood of the base. No compact set containing
all competing paths is a hypothesis. With a compact exhaustion and the slab
bound, reduced volume tends to (4*pi)^(n/2) at zero. Disjoint stable images
have additive reduced volume, and a fixed W's terminal-image lower bound
holds through its terminal time, as required by Theorem 8.1 (4)-(5).
The paired Jacobi term uses
g(R(Y,A)A,W), matching equation (6.6).
M13 parabolic rescaling identities are consumed
from the preceding rescaling theory. For every prescribed Q > 0 and shift a,
construct the analytic target with clock Q*(t-a), the exact transformed
interval, metric Q*g, and time vector chi/Q. The identity diffeomorphism,
horizontal and slice differentials identify the same geometric objects.
M13's metric-homothety calculus on those slices supplies connection,
curvature and volume scaling, with M12's Levi-Civita uniqueness identifying
the selected leafwise connections;
the normalized initial-vector map divides the horizontal map by sqrt(Q).
Action scales by sqrt(Q), reduced length is invariant on its finite domain,
and one selected target exponential family agrees pointwise with the
original on its domain, including square-root time zero. Its joint domains
and stable images use that same family; the Jacobian and density factors cancel.
The construction is conditional on
finite action, survival, and regular-domain hypotheses and makes no blanket
completeness claim for a generalized spacetime.
The applicable project corrections are `reviews/contracts/M08-repair-contract.md`,
`reviews/errata/2026-09-13-reduced-length-source.md`, and
`reviews/errata/2026-09-11-tensor-evolution.md`. The analytic rescaling follows
Lemma 6.72 (p. 141), Corollary 6.74 and Lemma 6.75 (p. 142), and the primitive
interface correction in `reviews/contracts/M11-M25-primitive-refactor-round1.md`.
Further clock, capture and survival corrections are derived in
`reviews/contracts/M11-M25-primitive-followup-round1.md`, following Definition
6.25, Definition 6.45, Lemma 6.49, Proposition 6.56 and Proposition 6.81.
The curvature-slot and slab corrections are recorded in
`reviews/contracts/2026-09-15-m14-m15-correction-round1.md`.
The complete public scope and ordinary subset transports are recorded in
`reviews/contracts/2026-09-17-m14-m15-full-review-round1.md`.
-/
theorem generalizedLGeometryTheory
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hM13 : GeneralizedParabolicRescalingTheory.{u} n)
    (hM04 : RicciFlowCurvatureTheory.{u}) :
    GeneralizedLGeometryTheory.{u} n := by
  cases hM04
  refine ⟨?_⟩
  intro X _ time I G
  exact ⟨M14.generalizedLGeometryConclusion_of_smallTimeCoverage
    (m12MetricPredecessors.{0} n) ricciFlowCurvatureTheory.{0} hM12 hM13 G
    (M14.smallTimeCoverageStatement (m12MetricPredecessors.{0} n) hM12 G)⟩

/-- Supply M14's actual M04/M12/M13 services. The ordinary-capture conclusion
still requires the caller's M08/M09/M10 provider; this assembly does not supply
it. Sources and qualifications are those of the complete statement above. -/
theorem generalizedLGeometryTheory_from_predecessors (n : ℕ) :
    GeneralizedLGeometryTheory.{u} n :=
  generalizedLGeometryTheory
    (generalizedRicciGaugeGeometry_from_M03_M04_M11 n)
    (generalizedParabolicRescaling_from_M12 n) ricciFlowCurvatureTheory

end PoincareMT
