import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Theory
import PoincareLib.Geometry.RicciFlow.Generalized.Noncollapse.Theory
import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.RegularHistory
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.CanonicalData
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.NoncollapseTheory
import PoincareLib.Geometry.RicciFlow.Curvature.Theory
import PoincareLib.Geometry.RicciFlow.Rescaling.Theory
import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Theory
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.ScalarPersistence
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.ComponentInputs
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.PositiveComponent.Statement

/-!
# M47 repaired canonical-neighborhood induction statement

Natural-language theorem: after the actual M04, M08-M15, geometric M30
compactness and M33 regular-history services are fixed at the theorem entry,
every calibrated surgery setup and every concrete
M46-indexed noncollapsing package on its compatible prefixes, each such finite
prefix and its noncollapsing extension admit positive next canonical
radius and surgery-control cutoff data satisfying the bounds and
canonical-neighborhood conclusion of Proposition 17.1.

Source: Morgan--Tian, Proposition 17.1, printed p. 395, with the
contradiction and compactness argument continuing through pp. 395--409.
The exact primitive output is `SurgeryCanonicalExtension`; its fields retain
the next-radius bound, cutoff bound, old-prefix overlap control, and the
canonical conclusion on the observed next epoch. The extension is the exact
one selected by the M46 package at that prefix; the theorem does not
quantify over an unrelated noncollapsing extension.

The same admission owns local scalar persistence, weak-2C component
analytic bounds, and uniform terminal scalar blow-up of a compact connected
initially strictly positive ordinary component. Their primitive statements
are in the three M47 supporting statement files. The positive-history and
volume constructions are proof work, not additional caller hypotheses.
The complete derivation and source qualifications are recorded in
reviews/contracts/2026-09-20-m47-complete-contract.md.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-- Earlier services used by the canonical first-failure argument. The exact
    M28/M27 applications and M44 cap persistence are retained by the supplied
    calibrated setup; no additional unaligned threshold is selected here. -/
structure M47Predecessors : Prop where
  m04 : RicciFlowCurvatureTheory.{u}
  ordinary : M14OrdinaryProviders.{u} 3
  m11 : GeneralizedSpacetimeGeometryTheory.{u} 3
  m12 : GeneralizedRicciGaugeTheory.{u} 3
  m13 : GeneralizedParabolicRescalingTheory.{u} 3
  m14 : GeneralizedLGeometryTheory.{u} 3
  m15 : GeneralizedNoncollapsingConclusion.{u} 3
  geometric_limits : ∀ (S : GeneralizedBlowupSequence.{u}) (T₀ : ℝ≥0∞),
    M30GeometricLongControls S T₀ →
    Nonempty (GeneralizedBlowupConvergence S (blowupBackwardInterval T₀))
  regular_history : ∀ (F : SurgeryFlowData.{u}) (W : M33RegularHistoryWindow F),
    Nonempty (M33RegularHistoryData W)

structure RepairedCanonicalInductionTheory : Prop where
  local_scalar_persistence : M47ScalarPersistencePredecessors.{u} →
    M47LocalScalarPersistenceStatement.{u}
  /-- The actual weak-2C component branch, with constants chosen before
      surgery heights and no supplied ordinary history. -/
  component_analytics : M47ComponentAnalyticPredecessors.{u} →
    ∀ C : ℝ, 1 ≤ C → Nonempty (M47ComponentAnalyticBounds.{u} C)
  /-- Strict positivity and connectedness are essential to the uniform
      terminal conclusion used to exclude a partially surviving component. -/
  positive_component_blowup : M47PositiveComponentBlowupStatement.{u}
  induction : ∀ S : RepairedControlledSchedulesData.{u},
      ∀ N : RepairedNoncollapseInductionData.{u} S,
      Nonempty (RepairedCanonicalInductionData S N)

end PoincareMT
