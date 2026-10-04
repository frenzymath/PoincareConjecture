import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Integrability
import PoincareLib.Geometry.Riemannian.LoopSpace.Area.Theory

/-!
# The actual C1 sphere functionals

The area and energy part of Morgan-Tian Lemma 18.10, printed pp. 424-426:
both densities are integrable, area is nonnegative and at most energy,
and weak conformality gives equality with the half-energy normalization.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareMT

/-- All area-energy conclusions for a fixed C1 sphere map and target metric.
Source: MT Lemma 18.10, printed pp. 424-426. -/
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

end PoincareMT
