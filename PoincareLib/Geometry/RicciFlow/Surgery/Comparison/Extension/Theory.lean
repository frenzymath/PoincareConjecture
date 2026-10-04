import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Map
import PoincareLib.Topology.Manifold.ConnectedSum.Surgery.Local
/-!
# SurgeryComparison repaired comparison-map statement

The geometric comparison uses a selected M38 local topology witness and
strong admissibility at each nonempty event after a uniform small-epsilon
choice. One map retains the limit isometry, sends the complement into the
actual closed caps, and has global near-unit Lipschitz bounds as the pre-time
approaches surgery. Homotopy, smoothing and degree transport stay in SurgeryComparison.Transport.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/- Morgan--Tian Proposition 15.12 (printed p. 365) and Claim 18.22
   (p. 433), using Claim 13.1/Theorem 13.2 (pp. 331--334).
   Choose a positive epsilon threshold before the standard metric and flow.
   For every strongly admissible nonempty surgery event below the terminal
   accuracy threshold and the strict delta/height cutoffs, take actual parent
   and child components, their pulled-back metrics, separating neck spheres,
   a selected local topology witness, and the full nonempty inherited open
   set fixed by `retained_eq`. Construct one continuous map extending the
   retained limit isometry with open retained target image. Its complement
   maps into the actual closed caps. For every eta > 0, the same map is
   (1 + eta)-Lipschitz for all sufficiently late actual pre-time metrics.
   The local collapse's constant tail glues the discarded branches; compact
   regular metric convergence supplies the eta-dependent time window.
   This is the near-unit consequence needed by Claim 18.22, not verbatim
   coverage of Proposition 15.12's exact-unit clause. Remark 15.13 records
   the nonseparating obstruction. See the source derivation in
   `reviews/contracts/2026-09-18-m39-repair-contract.md` and the unresolved
   legacy exact-unit boundary in
   `reviews/errata/2026-09-18-m39-comparison-provenance.md`. -/
structure RepairedComparisonMapTheory : Prop where
  comparison : ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧
    ∀ {g₀ : StandardInitialMetric},
      ∀ D : RepairedSurgeryFlowData.{u} g₀,
        terminalAccuracyFactor * D.flow.parameters.epsilon ≤ epsilon₀ →
        Nonempty (RepairedComparisonMapData D)

end PoincareMT
