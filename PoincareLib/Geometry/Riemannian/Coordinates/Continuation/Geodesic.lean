import PoincareLib.Geometry.Riemannian.Coordinates.Length
import PoincareLib.Geometry.Riemannian.Coordinates.Geodesic

/-! # Geodesics represented in local charts

The affine geodesic equation is required on a neighborhood of each parameter.
The chart can vary along the curve.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareMT.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- The affine geodesic equation, expressed locally in metric coordinates. -/
def IsGeodesicOn (g : RiemannianMetric n M) (γ : ℝ → M) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, ∃ p : M, ∃ q w : ℝ → EuclideanSpace ℝ (Fin n),
    ∀ᶠ u in 𝓝 t,
      γ u = (extChartAt (𝓡 n) p).symm (q u) ∧
      q u ∈ (extChartAt (𝓡 n) p).target ∧
      HasDerivAt q (w u) u ∧
      HasDerivAt w
        (-coordinateChristoffel
          (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm)
          (q u) (w u) (w u)) u

end PoincareMT.RiemannianMetric
