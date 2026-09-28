import PoincareConjecture.Definitions.M33BranchContinuation
import PoincareConjecture.Definitions.M33RegularHistory
import PoincareConjecture.Statements.Ch04.Continuation
import PoincareConjecture.Statements.Ch04.Pinching
import PoincareConjecture.Statements.M31SingularRegularLimit
import PoincareConjecture.Statements.M32HornSelection
















































set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture



structure M33Predecessors : Prop where
  local_flow : ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M],
      RicciFlowLocalTheory 3 M
  pinching : ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M],
    ∀ a b : ℝ, 0 ≤ a → a < b → ∀ F : RicciFlow 3 M (Set.Ico a b),
      HamiltonIveyPinchedAt (F.connection a) a → HamiltonIveyPinchingConclusion a b F

structure RepairedBranchContinuationTheory : Prop where
  regular_history : ∀ (F : SurgeryFlowData.{u}) (W : M33RegularHistoryWindow F),
    Nonempty (M33RegularHistoryData W)
  continuation : ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M],
    ∀ {F : SurgeryFlowData.{u}} {T : ℝ},
    ∀ I : RepairedContinuationInput F T,
    ∀ {G : GeneralizedRicciFlowData.{u}},
    ∀ H : SingularTimeAssumptions G T M,
    ∀ L : RepairedSingularRegularLimitData H,
    ∀ N : RepairedHornSelectionData H,
    RepairedContinuationLimitBridge H L N I →
      Nonempty (RepairedBranchContinuationData I)

end PoincareConjecture
