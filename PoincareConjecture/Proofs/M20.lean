import PoincareConjecture.Statements.M20ThreeDimensionalClassification
import PoincareConjecture.Proofs.M03
import PoincareConjecture.Proofs.M19
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Classification.Assembly

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

theorem m20CompactLocalFlowProvider_from_M03 :
    ∀ (n : ℕ) (N : Type u) [TopologicalSpace N] [T2Space N]
      [SecondCountableTopology N]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
      [IsManifold (𝓡 n) ∞ N] [CompactSpace N],
      RicciFlowLocalTheory n N := by
  intro n N _ _ _ _ _ _
  exact ricciFlowLocalTheory (n := n) (M := N)

theorem m20TwoDimensionalProvider_from_M19
    (hP : ∀ {N : Type u} [TopologicalSpace N]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N]
      [IsManifold (𝓡 2) ∞ N] [MeasurableSpace N] [BorelSpace N]
      [T2Space N] [T3Space N] [SecondCountableTopology N] [ConnectedSpace N],
      TwoDimensionalClassificationPredecessors (M := N)) :
    ∀ {N : Type u} [TopologicalSpace N]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N]
      [IsManifold (𝓡 2) ∞ N] [MeasurableSpace N] [BorelSpace N]
      [T2Space N] [T3Space N] [SecondCountableTopology N] [ConnectedSpace N],
      TwoDimensionalClassificationTheory (M := N) := by
  intro N _ _ _ _ _ _ _ _ _
  exact twoDimensionalAncientAndShrinkingSolitonClassification hP

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

theorem threeDimensionalAncientAndShrinkingSolitonClassification
    (P : ThreeDimensionalClassificationPredecessors.{u}) :
    ThreeDimensionalClassificationTheory (M := M) := by
  exact horizon_threeDimensionalAncientAndShrinkingSolitonClassification P

theorem threeDimensionalClassificationTheory
    (P : ThreeDimensionalClassificationPredecessors.{u}) :
    ThreeDimensionalClassificationTheory (M := M) := by
  exact threeDimensionalAncientAndShrinkingSolitonClassification P

end PoincareConjecture
