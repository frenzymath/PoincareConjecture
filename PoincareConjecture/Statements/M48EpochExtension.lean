import PoincareConjecture.Definitions.M48EpochExtension
import PoincareConjecture.Definitions.M48AnalyticCalibration
import PoincareConjecture.Statements.M43UnifiedContinuation
import PoincareConjecture.Statements.M33BranchContinuation
import PoincareConjecture.Statements.M31SingularRegularLimit
import PoincareConjecture.Statements.M32HornSelection
import PoincareConjecture.Statements.M36MetricSurgery
import PoincareConjecture.Statements.M46NoncollapseInduction
import PoincareConjecture.Statements.M47CanonicalInduction













































set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture




structure M48Predecessors : Prop where
  m11 : GeneralizedSpacetimeGeometryTheory.{u} 3
  m12 : GeneralizedRicciGaugeTheory.{u} 3
  m13 : GeneralizedParabolicRescalingTheory.{u} 3
  m31 : RepairedSingularRegularLimitTheory.{u}
  m32 : RepairedHornSelectionTheory.{u}
  m33 : RepairedBranchContinuationTheory.{u}
  m36 : RepairedMetricSurgeryTheory.{u}
  m43 : RepairedUnifiedContinuationTheory.{u}

structure RepairedEpochExtensionTheory : Prop where
  one_step : M48Predecessors.{u} →
    ∀ S : RepairedControlledSchedulesData.{u},
    M48AnalyticCalibration S →
    ∀ N : RepairedNoncollapseInductionData.{u} S,
      ∀ C : RepairedCanonicalInductionData S N,
        Nonempty (RepairedEpochExtensionData S N C)

end PoincareConjecture
