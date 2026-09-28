import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.StationaryEnergyTests
import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.WeakChartHarmonicity









set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem m60EnergyStationary_chartHarmonic (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (hstat : M60EnergyStationary g f) : M60SphereChartHarmonic g f := by
  exact m60SphereChartHarmonic_of_test_integrals g f hf
    (m60EnergyStationary_test_integral_eq_zero g f hf hstat)

end PoincareConjecture
