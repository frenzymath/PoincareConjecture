import PoincareLib.Geometry.Riemannian.Metric.LocalDiffeomorph
import PoincareLib.Geometry.RicciFlow.MetricFamily.Descent

/-! # Smooth metric families under a fixed local diffeomorphism -/

set_option autoImplicit false
open Set
open scoped Manifold ContDiff

namespace PoincareMT.RiemannianMetric

theorem IsSmoothFamilyOn.pullbackOfLocalDiffeomorph
    {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
    {g : ℝ → RiemannianMetric n N} {J : Set ℝ}
    (hg : IsSmoothFamilyOn g J) (f : M → N)
    (hf : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ f) :
    IsSmoothFamilyOn (fun t => (g t).pullbackOfLocalDiffeomorph f hf) J := by
  rintro ⟨t, x⟩ ⟨ht, _⟩
  exact Poincare.Gluing.inducedForm_family_contMDiffWithinAt hg (hf.contMDiff x) ht

end PoincareMT.RiemannianMetric
