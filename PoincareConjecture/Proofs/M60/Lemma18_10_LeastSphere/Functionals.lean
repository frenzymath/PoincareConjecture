import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.Integrability
import PoincareConjecture.Statements.M60Area

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

theorem m60SphereAreaProperties_of_contMDiff
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (f : UnitTwoSphere → M)
    (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f) : M60SphereAreaProperties g f where
  area_integrable := m60SphereAreaDensity_integrable g f hf
  energy_integrable := m60SphereEnergyDensity_integrable g f hf
  area_nonnegative := m60SphereArea_nonneg g f
  area_le_energy := m60SphereArea_le_energy_of_integrable g f
    (m60SphereEnergyDensity_integrable g f hf)
  conformal_equality := m60SphereArea_eq_energy_of_weaklyConformal g f hf

end PoincareConjecture
