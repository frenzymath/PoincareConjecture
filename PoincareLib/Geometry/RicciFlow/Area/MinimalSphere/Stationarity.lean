import PoincareLib.Geometry.RicciFlow.Area.MinimalSphere.Variation.EnergyTests
import PoincareLib.Geometry.RicciFlow.Area.MinimalSphere.WeakChartHarmonicity

/-!
# Energy stationarity gives the actual harmonic equation

Morgan-Tian Claim 18.12, printed pp. 426-427. Smooth supported coordinate
variations differentiate the actual energy. Their vanishing first
variations imply zero coordinate tension by integration by parts.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- The frozen energy-stationarity predicate implies the actual chart
harmonic equation. Source: MT Claim 18.12, pp. 426-427. -/
theorem m60EnergyStationary_chartHarmonic (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (hstat : M60EnergyStationary g f) : M60SphereChartHarmonic g f := by
  exact m60SphereChartHarmonic_of_test_integrals g f hf
    (m60EnergyStationary_test_integral_eq_zero g f hf hstat)

end PoincareMT
