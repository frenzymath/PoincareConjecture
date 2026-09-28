import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Curvature.Control
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.ScaleComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.Containment

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck

theorem exists_nearby_scale_and_containment :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} (N N' : EpsilonNeck g),
        N.epsilon ≤ ε₀ →
        N'.center ∈ N.region (-N.epsilon⁻¹ / 2) (N.epsilon⁻¹ / 2) →
        N'.scale ≤ 2 * N.scale ∧ N'.central_sphere ⊆ N.carrier := by
  obtain ⟨ε₁, hε₁, hε₁small, hcurv⟩ :=
    exists_ambient_curvature_control.{u} (α := 1 / 2) (by norm_num)
  obtain ⟨ε₂, hε₂, _, hcontain⟩ := exists_central_sphere_subset_threshold.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hε₁small, ?_⟩
  intro M _ _ _ _ _ _ _ g N N' hε hcenter
  have hs := (N.coordinate_inverse_mem N'.center hcenter.1).2
  have hscalar : |N.scale ^ 2 * N.connection.scalarCurvature N'.center - 1| < 1 / 2 := by
    simpa only [Prod.eta, N.coordinate_map_coordinate_inverse hcenter.1] using
      (hcurv N N.connection (hε.trans (min_le_left _ _))
        (N.coordinate_inverse N'.center).1 hs).1
  have hscale := N.scale_le_two_mul_of_normalized_scalar_close N' hscalar
  exact ⟨hscale, hcontain N N' (hε.trans (min_le_right _ _)) hscale hcenter⟩

end PoincareConjecture.EpsilonNeck
