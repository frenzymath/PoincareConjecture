import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt

/-!
# Local path connectedness of real manifolds with corners

Convexity of the model range gives local path connectedness, which transfers
through the model embedding and the manifold charts.
-/

noncomputable section

open Set

namespace Poincare.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

include I in
/-- Local path connectedness comes from the manifold model and chart maps. -/
theorem manifold_locallyPathConnected : LocallyPathConnectedSpace M := by
  let : LocallyPathConnectedSpace (range I) := I.convex_range.locallyPathConnectedSpace
  let : LocallyPathConnectedSpace H :=
    I.isClosedEmbedding.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H M

end Poincare.Manifold
