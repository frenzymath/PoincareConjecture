import PoincareConjecture.Statements.M19TwoDimensionalClassification
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

theorem twoDimensionalAncientAndShrinkingSolitonClassification
    (P : TwoDimensionalClassificationPredecessors (M := M)) :
    TwoDimensionalClassificationTheory (M := M) := by
  exact horizon_twoDimensionalAncientAndShrinkingSolitonClassification P

theorem twoDimensionalClassificationTheory
    (P : TwoDimensionalClassificationPredecessors (M := M)) :
    TwoDimensionalClassificationTheory (M := M) :=
  twoDimensionalAncientAndShrinkingSolitonClassification P

end PoincareConjecture
