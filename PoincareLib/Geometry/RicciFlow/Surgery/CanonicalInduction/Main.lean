import PoincareLib.Geometry.RicciFlow.Surgery.Induction.CanonicalTheory
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Extension.CanonicalControls
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Regular.RegularHistory
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Terminal.Components.TerminalComponents
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Induction.InductionCompletion

/-!
# M47 canonical-neighborhood induction

-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-
Natural-language theorem: after the actual M04 curvature theory,
dimension-three M08-M10 ordinary providers, M11/M12 generalized geometry,
M13 rescaling, M14 L-geometry, M15 generalized noncollapsing, M30 geometric
compactness and M33 regular-history services are fixed,
every calibrated surgery setup and every M46 noncollapsing package has, at
every compatible finite prefix with i > 0, a canonical extension. The
extension chooses a positive next canonical radius no larger than the last
radius and a positive delta no larger than the M46 cutoff at that radius. It
then supplies the strong canonical-neighborhood conclusion under the exact
old-prefix, observed Definition 15.8 terminal policy, pinching, admissibility, post-prefix-scale,
and overlap hypotheses carried by the primitive `SurgeryCanonicalExtension`.
The noncollapsing extension in that output is the prefix-indexed extension
selected by the M46 package itself.
Theorem 10.2 and the kappa-solution canonical/derivative estimates are the
actual calibrated applications retained by the supplied M45 setup. M47
constructs the controlled cylinders and volume needed by its M30 service;
the service itself is not a premise asserting those geometric inputs.
No endpoint, global flow, or finite-extinction conclusion is asserted here.
`RegularHistory` applies M33 on the closed included history up to a positive
nonempty test time, with the original absolute clock. It retains the exact
regular image; exposed-cap exclusion, backward survival and all M30
curvature/volume hypotheses remain part of the first-failure proof.
`TerminalComponents` identifies retained compact terminal components with
the literal whole pre/post components and proves the post-metric pullback
identity for the limit metric. Ordinary-history assembly and the uniform
volume seed for components born at surgery are owned by this admission.
The complete source derivation, including constant order and the old/recent
history split, is in `reviews/contracts/2026-09-20-m47-complete-contract.md`.

The same admission also owns this local supporting theorem: given the three
M04 scalar-calculus services, K>0 and a>0 determine a positive duration before
the three-manifold and ordinary flow are chosen. If its initial a-ball has
compact closure, |Rm|<=K and R>=-1 on the fixed ball throughout [0,T], and
R>=3/4 initially on that ball, then R at its center remains at least 1/4
through min(T,duration). Its statement has no surgery or noncollapse premise.

The component supporting output uses those three scalar services plus M04
local Shi estimates and metric comparison. Given C>=1, choose a positive
duration, high-curvature threshold and analytic coefficient before any
standard model or flow, then a cutoff for each actual standard model and
metric-surgery constants. On a raw flow with those data, pinching on the
displayed backward interval, earlier strong canonical control above the
base scalar Q, and surgery delta below that cutoff, an actual terminal
2C-component containing the basepoint has the scalar gradient and absolute
spatial evolution bounds with the selected coefficient. Q is the actual
base scalar and is at least the selected threshold. The flow's epsilon is at
most 1/200. No analytic estimate, noncollapse or history is a premise.

The fourth output concerns an ordinary flow on [0,T), T>0, on a compact
connected smooth three-manifold. If all sectional curvatures at time zero
are strictly positive and full curvature is unbounded arbitrarily near T,
then for every L there is s in [0,T) such that R(x,t)>=L for all x and
s<t<T. ConnectedSpace includes nonemptiness. This is the strictly positive
case of Hamilton's Theorem 4.23, pp. 74-75; the printed general
nonnegative-Ricci dichotomy is not asserted. This is a supporting output,
not a premise that a surgery component already has the required history.

M47 constructs the history by excluding a backward scalar crossing with
local persistence and excluding a cap encounter by the actual event's
local_result.standard_close and a compact-chart diameter argument. Existing
slabs are glued using fixed transition diffeomorphisms and their metric
jets; their time-dependent identifications are not differentiated. Constant
rescaling, curvature naturality and contractions are internal proof work.
The fixed Type-0 standard-tip accuracy uses its actual coordinate two-jet.
The geometric-first-failure argument also constructs volume on positive
components. Historical cap contacts use a fixed scalar-level neck/cap seed
and a bounded chain of local volume comparisons, with no new historic
comparison cutoff. Recent barriers fit the existing overlap interval.
M15 is applied at a fixed smaller tested radius when required by its
backward-time bound. These constructions remain proof work inside M47.

Source: Morgan--Tian, Proposition 17.1, printed p. 395; its contradiction
argument and the compactness/canonical-neighborhood analysis run through
printed pp. 395--409. The preceding noncollapsing input is Proposition 16.1
(M46), while the source's fixed sequences and next-radius cutoff are exposed
by the compatible finite prefixes and the M46 `SurgeryNoncollapseExtension`.
See `reviews/contracts/2026-09-15-m45-finite-prefix-round1.md` for the
finite-prefix correction.
The source proposition does not assume a scalar-time-derivative estimate;
Claim 17.9 invokes an absolute derivative bound during the canonical
first-failure analysis. The separate component output and the actual
calibrated neck/cap/round estimates supply its analytic branches. Retain
Q>=rNext^(-2), not an assumed equality. In the terminal null-curvature
case, use compatible local backward germs before constructing the common
ancient interval, as recorded in
`reviews/contracts/2026-09-18-m47-terminal-germ-curvature.md`.
The observation excludes its horizon; the maximal adapter uses the actual
domain equality without changing the Icc test cylinders. A terminal surgery
needs its own endpoint cutoff hypothesis.
Local support: equation (3.7), p. 41, and the local-cover/cutoff argument,
pp. 52--54, retaining MT-SHI-CUTOFF-SPACETIME. The derived persistence
statement and its separate application boundary are reviewed in
`reviews/contracts/2026-09-15-m47-scalar-persistence-round1.md`.
Component support: Definitions 9.72, 9.75 and 9.76, pp. 230-231;
Theorem 13.2, pp. 332-333; the first-failure argument, pp. 402-405;
and the corrected local Shi estimates. Its derivation and application
boundary are in `reviews/contracts/2026-09-15-m47-component-analytics-round1.md`.
The earlier bounded predecessor correction is recorded in
`reviews/contracts/2026-09-18-m47-provider-contract.md`; the complete
September 20 contract supersedes its source hold without completing this proof.
-/

theorem repairedCanonicalInduction (P : M47Predecessors.{u}) :
    RepairedCanonicalInductionTheory.{u} :=
  Proofs.M47.canonicalInductionTheory_of_induction P (M47.canonicalInduction P)

end PoincareMT
