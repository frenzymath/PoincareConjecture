import PoincareLib.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Assembly.Completion
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.LimitTheory
import PoincareLib.Geometry.RicciFlow.Curvature.Construction
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.Sequences.RegularCanonical

/-!
# M31 singular-time regular-limit proof entry

The numbered theorem owns the construction of the complete linked
`SingularLimitConclusion`; later milestones may use its terminal extension and
end/canonical-neighborhood fields without reconstructing the gluing data.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-
Given the actual M04 curvature theory, Morgan--Tian Theorem 11.19
(printed pp. 279--280), using the reviewed regular-time extension of Assumptions 11.18,
Lemmas 11.2 and 11.21--11.30 (pp. 280--287), and Definition 11.22:
for a generalized Ricci flow on 0 <= t < T with discrete singular times,
compact nonsingular slices, positive pinching, and the stated derivative and
canonical-neighborhood bounds at time zero and nonsingular times, the finite-liminf
set Omega in the fixed preterminal slice is open. The pulled-back metrics converge to a smooth
terminal metric uniformly in C-infinity on compact subsets of Omega; terminal
scalar curvature is proper and bounded below; the preterminal flow extends by
the exact old-time/terminal gluing construction; every end of each connected
component lies in a strong 2 epsilon tube; and every terminal point above the
r0 curvature threshold has a strong (2 C, terminalAccuracyFactor * epsilon)-canonical
neighborhood (revision of 2026-09-22: the printed factor two is not attainable
in the cap case of Proposition 9.79(3); see `terminalAccuracyFactor`).
The complete conclusion is `SingularLimitConclusion`, which permits an empty
terminal regular set and does not assert completeness of that slice.
Choose the epsilon threshold before the reference manifold and flow, below
the supplied M25 threshold divided by `terminalAccuracyFactor` and within the
source's Proposition 2.19 regime. The primitive
input also records the numeric cap-certificate ceiling
`terminalAccuracyFactor * epsilon ≤ 1 / 200` at the terminal accuracy.
The guarded derivative bounds use a separate positive analytic coefficient.
It affects Lemma 11.21's local windows; Lemma 11.23 takes limits of the
original (C, epsilon) neighborhoods and produces (2 C, terminalAccuracyFactor * epsilon)
by the same-core route: keep the old core and the center of its boundary neck,
shorten and recenter the old end neck, and renormalize at the new center.
Isolation of T supplies a nonsingular final collar. Earlier analytic work
keeps its all-time bounds, and `RegularCanonical` proves the dense-time adapter.
See `reviews/contracts/2026-09-18-regular-time-canonical-boundary-round1.md`.
See `reviews/contracts/2026-09-15-analytic-selector-round1.md`.

The source contract is Morgan--Tian Theorem 11.19, Definition 11.22 and
Definitions 11.25--11.27. Apply the endpoint and incomplete-limit conventions
from `reviews/errata/2026-09-10-source-audit.md` and the topology note
`MT-NECK-SEPARATION` in `reviews/errata/2026-09-10-analytic-outline-audit.md`;
no M26/M27/M30 theorem output is a direct premise because the canonical and
scalar derivative controls are primitive fields of `SingularTimeAssumptions`.
M04 supplies the higher curvature derivative estimates used in Lemma 11.21.
The fixed reference manifold is compact by the discrete catalog and its
surjective identification with a compact regular slice. See the complete
derivation in `reviews/contracts/2026-09-17-m31-full-contract.md`, including
the corrected normalized clock in Claim 11.24.
-/
theorem m31SingularRegularLimitStatement (P04 : RicciFlowCurvatureTheory.{u}) :
    ∀ A : RepairedNeckCapTopologyTheory.{u},
      ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ terminalAccuracyFactor * epsilon₀ ≤ A.epsilon₀ ∧
        ∀ {M : Type u} [TopologicalSpace M]
          [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
          [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
          [T2Space M] [T3Space M] [SecondCountableTopology M]
          {F : GeneralizedRicciFlowData.{u}} {T : ℝ},
          ∀ H : SingularTimeAssumptions F T M,
            H.epsilon ≤ epsilon₀ →
              Nonempty (RepairedSingularRegularLimitData H) :=
  (m31SingularRegularLimit P04).limit


/-! No-sorry theory assembly used by downstream milestone interfaces. -/
theorem m31SingularRegularLimitTheory : RepairedSingularRegularLimitTheory.{u} := by
  exact ⟨m31SingularRegularLimitStatement ricciFlowCurvatureTheory⟩

end PoincareMT
