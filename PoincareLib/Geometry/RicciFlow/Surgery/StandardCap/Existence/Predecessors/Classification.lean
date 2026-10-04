import PoincareLib.Geometry.RicciFlow.Soliton.ThreeDimensional.Classification.Assembly
import PoincareLib.Geometry.RicciFlow.Curvature.Construction
import PoincareLib.Geometry.RicciFlow.Local.ExistenceUniquenessContinuation
import PoincareLib.Geometry.RicciFlow.Soliton.TwoDimensional

/-! Source predecessor applications; existing geometric proofs are reused. -/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

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

end PoincareMT
