import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.UniquenessTheory
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Predecessors
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.MetricUniqueness.LifetimeEquality
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.MetricUniqueness.PartialUniqueness
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.CapGeometry.IndependentScalarRate
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.CapGeometry.CanonicalAlternatives

/-!
# M35 standard-cap uniqueness and estimates proof entry

The numbered theorem assembles uniqueness, lifetime, the scalar lower rate
and the three canonical alternatives on the supplied standard-cap flow.
Supporting objects are declared in `Definitions/M35StandardCapUniqueness.lean`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareMT

/-- M35: for every standard initial metric and supplied M34 existence datum E,
the same selected flow is complete on [0,1) and has lifetime one. Every raw
maximal standard flow from that initial metric has the same lifetime and
the same metric at every time in the intersection of their domains. Every raw
partial standard flow with the same initial data agrees with the selected
flow on the common domain. No completeness, rotation or asymptotic conclusion
is assumed for those raw flows.

There is c > 0, chosen before the point and time, with R_E(x,t) >= c/(1-t).
For every 0 < epsilon < 1/2 there is C > 0, chosen before the point and time,
such that every (x,t) lies in the core of a quantitative Euclidean cap,
is centered in an evolving epsilon-neck on the actual interval [0,t]
disjoint from the closed radius-(A0+4) ball in the initial standard metric,
or is centered in one on normalized time
(-(1+epsilon),0]. The actual caps have the stated scalar, intrinsic diameter,
volume, ambient core-ball, gradient and absolute scalar-time bounds.
One fixed spatial map compares each neck with the literal evolving cylinder
in the intrinsic spatial norm through order floor(1/epsilon).

Sources: Morgan-Tian Theorem 12.5, pp. 295-296, and the uniqueness argument,
pp. 307-323; Proposition 12.31, pp. 325-326; Theorem 12.32, pp. 326-327;
Definition 13.3 and Lemma 13.4, pp. 333-334 (surgery cap), using the unit
distance margin in the proof of Theorem 12.32; Definition 2.16 and
Remark 2.17, p. 30. The supplied earlier services are
full M04 curvature theory, compact dimension-two M03 uniqueness, M07
compactness, M13 rescaling and metric transport, and M27/M30 on the same
selected ancient limit. M34's datum is the actual geometric input.

Common-domain uniqueness uses M34's published native energy theorem for
arbitrary partial standard-cap flows. The proof then supplies exact
old-connection splicing, ordinary-to-generalized realization and finite-jet
transport. First obtain fixed unit-time canonical
and absolute analytic controls and the scalar rate. A separate limit argument
with diverging candidate cap constants gives the exact extra-time alternative;
Corollary 9.95's unspecified extension is not identified with epsilon.
The independent radial gauge development uses -xi and retains its possible
O(1/r) displacement.
See `reviews/contracts/2026-09-17-m35-full-contract.md`, the initial-cap
correction in `reviews/contracts/2026-09-19-m18-m35-boundaries-round1.md`, and
`reviews/errata/2026-09-17-m35-radial-gauge.md`, together with the compactness,
time-endpoint, scalar-ODE and DeTurck-sign corrections named there. -/
theorem repairedStandardCapUniqueness (P : M35StandardCapPredecessors) :
    RepairedStandardCapUniquenessTheory := by
  refine ⟨?_⟩
  intro g₀ E
  have hunique (G : PartialStandardCapFlow g₀) (t : ℝ)
      (ht : t ∈ Set.Ico 0 E.flow.base.lifetime ∩ Set.Ico 0 G.lifetime) :=
    E.partial_metric_unique P.curvature G ht
  refine ⟨{
    lifetime_one := E.lifetime_one
    complete := E.complete
    unique_lifetime := ?_
    unique_metric := fun G t ht => hunique G.base t ht
    partial_unique_metric := hunique
    scalar_lower_bound := E.scalar_lower_rate_from_unit_time P
    canonical := M35.Uniqueness.standard_cap_canonical P E
  }⟩
  intro G
  exact E.flow.lifetime_eq_of_metric_agreement G (fun t ht => hunique G.base t ht)

end PoincareMT
