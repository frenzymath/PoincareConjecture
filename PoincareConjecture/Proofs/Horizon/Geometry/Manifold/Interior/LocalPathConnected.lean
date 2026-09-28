import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt








noncomputable section

open Set

namespace Poincare.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

include I in

theorem manifold_locallyPathConnected : LocallyPathConnectedSpace M := by
  let : LocallyPathConnectedSpace (range I) := I.convex_range.locallyPathConnectedSpace
  let : LocallyPathConnectedSpace H :=
    I.isClosedEmbedding.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H M

end Poincare.Manifold
