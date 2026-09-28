import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Overlap.GraphProjection
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.NearbyContainment
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.ProjectionDerivative
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Curvature.Quadratic













set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck



theorem exists_nearby_graphical_sphere :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ},
        0 < ε → ε ≤ ε₀ → ∀ (N N' : EpsilonNeck g),
        N.epsilon = ε → N'.epsilon = ε →
        N'.center ∈ N.region (-ε⁻¹ / 2) (ε⁻¹ / 2) →
        ∃ h : UnitTwoSphere → ℝ, Continuous h ∧
          (∀ q, h q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) ∧
          N'.central_sphere = range (fun q => N.coordinate_map (q, h q)) := by
  obtain ⟨ε₁, hε₁, hε₁small, hcontain⟩ := exists_nearby_scale_and_containment.{u}
  obtain ⟨ε₂, hε₂, _, hricci⟩ := exists_ricci_quadratic_control.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hε₁small, ?_⟩
  intro M _ _ _ _ _ _ _ g ε _ hε N N' hN hN' hcenter
  obtain ⟨hscale, hsubset⟩ := hcontain N N'
    (hN ▸ hε.trans (min_le_left _ _)) (by simpa only [hN] using hcenter)
  apply N.exists_continuous_centralSphere_graph_of_isLocalHomeomorph N' hsubset
  apply N.centralSphere_projection_isLocalHomeomorph_of_bijective_mfderiv N' hsubset
  intro q
  exact N.centralSphere_projection_mfderiv_bijective_of_ricci_error N.connection N' q
    (hsubset (N'.centralSphere_range ▸ mem_range_self q)) hscale
    (hricci N N.connection (hN ▸ hε.trans (min_le_right _ _)))
    (hricci N' N.connection (hN' ▸ hε.trans (min_le_right _ _)))




theorem exists_nearby_compact_transport :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ},
        0 < ε → ε ≤ ε₀ → ∀ (N N' : EpsilonNeck g),
        N.epsilon = ε → N'.epsilon = ε →
        N'.center ∈ N.region (-ε⁻¹ / 2) (ε⁻¹ / 2) →
        ∃ (e : M ≃ₜ M) (K : Set M), IsCompact K ∧ K ⊆ N.carrier ∧
          (∀ x, x ∉ K → e x = x) ∧
          e '' connectedComponent N.center = connectedComponent N'.center ∧
          e '' N.central_sphere = N'.central_sphere := by
  obtain ⟨ε₀, hε₀, hε₀small, hgraph⟩ := exists_nearby_graphical_sphere.{u}
  refine ⟨ε₀, hε₀, hε₀small, ?_⟩
  intro M _ _ _ _ _ _ _ g ε hεpos hε N N' hN hN' hcenter
  obtain ⟨h, hh, hdom, hsphere⟩ := hgraph hεpos hε N N' hN hN' hcenter
  obtain ⟨r, hr, hrN, hbound⟩ := N.exists_graph_collar h hh hdom
  refine ⟨N.graphTransport hr hrN h hh hbound, N.closedCollar r,
    N.isCompact_closedCollar hrN, N.closedCollar_subset_carrier hrN,
    fun x hx => N.graphTransport_fixed hr hrN h hh hbound hx, ?_, ?_⟩
  · rw [N.graphTransport_image_connectedComponent]
    exact connectedComponent_eq (N.carrier_subset_connectedComponent hcenter.1)
  · exact (N.graphTransport_image_central_sphere hr hrN h hh hbound).trans hsphere.symm

end PoincareConjecture.EpsilonNeck
