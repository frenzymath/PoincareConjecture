import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Overlap.GraphProjection
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.ScaleComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.ProjectionDerivative
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Curvature.Quadratic

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck

theorem exists_contained_graphical_sphere :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ},
        0 < ε → ε ≤ ε₀ → ∀ (N N' : EpsilonNeck g),
        N.epsilon = ε → N'.epsilon = ε →
        N'.central_sphere ⊆ N.carrier →
        ∃ h : UnitTwoSphere → ℝ, Continuous h ∧
          (∀ q, h q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) ∧
          N'.central_sphere = range (fun q => N.coordinate_map (q, h q)) := by
  obtain ⟨ε₁, hε₁, hε₁small, hcurv⟩ :=
    exists_ambient_curvature_control.{u} (α := 1 / 2) (by norm_num)
  obtain ⟨ε₂, hε₂, _, hricci⟩ := exists_ricci_quadratic_control.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hε₁small, ?_⟩
  intro M _ _ _ _ _ _ _ g ε _ hε N N' hN hN' hsubset
  have hcenter : N'.center ∈ N.carrier := hsubset N'.center_on_central_sphere
  have hs := (N.coordinate_inverse_mem N'.center hcenter).2
  have hscalar : |N.scale ^ 2 * N.connection.scalarCurvature N'.center - 1| < 1 / 2 := by
    simpa only [Prod.eta, N.coordinate_map_coordinate_inverse hcenter] using
      (hcurv N N.connection (hN ▸ hε.trans (min_le_left _ _))
        (N.coordinate_inverse N'.center).1 hs).1
  have hscale := N.scale_le_two_mul_of_normalized_scalar_close N' hscalar
  apply N.exists_continuous_centralSphere_graph_of_isLocalHomeomorph N' hsubset
  apply N.centralSphere_projection_isLocalHomeomorph_of_bijective_mfderiv N' hsubset
  intro q
  exact N.centralSphere_projection_mfderiv_bijective_of_ricci_error N.connection N' q
    (hsubset (N'.centralSphere_range ▸ mem_range_self q)) hscale
    (hricci N N.connection (hN ▸ hε.trans (min_le_right _ _)))
    (hricci N' N.connection (hN' ▸ hε.trans (min_le_right _ _)))

theorem exists_contained_compact_transport :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ},
        0 < ε → ε ≤ ε₀ → ∀ (N N' : EpsilonNeck g),
        N.epsilon = ε → N'.epsilon = ε →
        N'.central_sphere ⊆ N.carrier →
        ∃ (e : M ≃ₜ M) (K : Set M), IsCompact K ∧ K ⊆ N.carrier ∧
          (∀ x, x ∉ K → e x = x) ∧
          e '' connectedComponent N.center = connectedComponent N'.center ∧
          e '' N.central_sphere = N'.central_sphere := by
  obtain ⟨ε₀, hε₀, hε₀small, hgraph⟩ := exists_contained_graphical_sphere.{u}
  refine ⟨ε₀, hε₀, hε₀small, ?_⟩
  intro M _ _ _ _ _ _ _ g ε hεpos hε N N' hN hN' hsubset
  obtain ⟨h, hh, hdom, hsphere⟩ := hgraph hεpos hε N N' hN hN' hsubset
  obtain ⟨r, hr, hrN, hbound⟩ := N.exists_graph_collar h hh hdom
  refine ⟨N.graphTransport hr hrN h hh hbound, N.closedCollar r,
    N.isCompact_closedCollar hrN, N.closedCollar_subset_carrier hrN,
    fun x hx => N.graphTransport_fixed hr hrN h hh hbound hx, ?_, ?_⟩
  · rw [N.graphTransport_image_connectedComponent]
    exact connectedComponent_eq
      (N.carrier_subset_connectedComponent (hsubset N'.center_on_central_sphere))
  · exact (N.graphTransport_image_central_sphere hr hrN h hh hbound).trans hsphere.symm

end PoincareConjecture.EpsilonNeck
