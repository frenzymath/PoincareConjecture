import PoincareLib.Geometry.RicciFlow.Extinction.Global.Definitions
import PoincareLib.Geometry.RicciFlow.Extinction.Width.Path.Theory
import PoincareLib.Geometry.RicciFlow.Extinction.Width.Profile.Theory
import PoincareLib.Geometry.RicciFlow.Extinction.Width.FinitePiece.Statement

/-!
# M71 conditional fixed-initial-class extinction statement

Natural-language theorem: for the actual M52 global changing-carrier flow,
given a same-flow M56 ancestry witness, one fixed time-zero component and
nonzero initial class with trivial pi2, target component covers normalized to
that initial component, strict delta/height bounds at all actual surgery times,
the actual-flow scalar bound, the indexed M58/M61/M65/M66 width services,
and the predecessor services for M67, M68, and M69,
the nonnegative width contradicts the explicit profile at a time depending
only on that fixed initial width. Therefore the flow has a finite
first empty time.  That time is an actual surgery time by the checked
first-empty policy, and emptiness persists on the remaining flow domain.  The
theorem does not construct a connected-sum assembly or either Poincare
endpoint.

This is the zero-time Poincare-branch application. M02 supplies the initial
pi2-trivial, pi3-integer class data, and M53/M55/M56 preserve the required
simply connected component path, so Proposition 18.9 is used with T1 = 0.
The general finite-pi1 late-start and W2 construction is outside the declared
endpoints and is not represented by an unused `late` field.

Source: Morgan--Tian Theorem 18.1, Proposition 18.9 and Claims 18.19-18.20,
printed pp. 415, 421-422 and 431-432; `reviews/contracts/2026-09-16-m71-fixed-class-round1.md` and
`reviews/errata/2026-09-16-m71-first-empty-policy.md`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

def M71GlobalFiniteExtinctionStatement : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [CompactSpace M]
    (N : NormalizedInitialMetric (M := M))
    (G : RepairedGlobalFlowData N),
    M71GlobalExtinctionInput N G →
      M67SurgeryWidthTheory.{u} →
      M68ScalarClockStatement.{u} →
      M69FinitePieceStatement.{u} →
      Nonempty (FiniteExtinctionConclusion G.certificate.flow)

end PoincareMT
