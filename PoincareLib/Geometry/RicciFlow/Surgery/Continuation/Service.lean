import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Branch
import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.RegularHistory

/-!
Adapted from Mapher `PoincareMT/Statements/M33BranchContinuation.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology BigOperators intervalIntegral

universe u

namespace PoincareMT


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

end PoincareMT
