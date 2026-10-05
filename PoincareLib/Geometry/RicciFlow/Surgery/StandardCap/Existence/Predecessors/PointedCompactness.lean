import PoincareLib.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Compactness
import PoincareLib.Geometry.RicciFlow.Curvature.Construction

/-! Source predecessor applications; existing geometric proofs are reused. -/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

theorem pointedRicciFlowCompactness_from_M04
    {n : ℕ} {T' T : ℝ}
    (H : PointedRicciFlowCompactnessHypotheses n T' T) :
    Nonempty (PointedRicciFlowCompactnessConclusion H) := by
  exact pointedRicciFlowCompactness H ricciFlowCurvatureTheory.{0}

end PoincareMT
