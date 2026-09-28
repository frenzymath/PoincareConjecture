import PoincareConjecture.Definitions.M71FiniteExtinction
import PoincareConjecture.Statements.M67
import PoincareConjecture.Statements.M68
import PoincareConjecture.Statements.M69




























set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

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

end PoincareConjecture
