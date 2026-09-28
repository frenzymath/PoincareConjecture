import PoincareConjecture.Definitions.M47CanonicalInduction
import PoincareConjecture.Statements.M46NoncollapseInduction
import PoincareConjecture.Statements.Ch04.CurvatureTheory
import PoincareConjecture.Statements.M13Rescaling
import PoincareConjecture.Statements.M30ControlledBlowupLimits
import PoincareConjecture.Statements.M47ScalarPersistence
import PoincareConjecture.Statements.M47ComponentAnalytics
import PoincareConjecture.Statements.M47PositiveComponent

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

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

  component_analytics : M47ComponentAnalyticPredecessors.{u} →
    ∀ C : ℝ, 1 ≤ C → Nonempty (M47ComponentAnalyticBounds.{u} C)

  positive_component_blowup : M47PositiveComponentBlowupStatement.{u}
  induction : ∀ S : RepairedControlledSchedulesData.{u},
      ∀ N : RepairedNoncollapseInductionData.{u} S,
      Nonempty (RepairedCanonicalInductionData S N)

end PoincareConjecture
