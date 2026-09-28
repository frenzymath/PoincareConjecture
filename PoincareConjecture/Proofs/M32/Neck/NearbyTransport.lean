import PoincareConjecture.Proofs.M32.Neck.ScalarControl
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Uniqueness
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Overlap.GraphProjection
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.Containment
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.ProjectionDerivative
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Curvature.Quadratic

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M32

section Scale

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem neckScale_sq_mul_scalar_center_of_connection (N : EpsilonNeck g)
    (D : LeviCivitaData g) : N.scale ^ 2 * D.scalarCurvature N.center = 1 := by
  have hscalar : D.scalarCurvature N.center = N.connection.scalarCurvature N.center := by
    unfold LeviCivitaData.scalarCurvature LeviCivitaData.ricci
    simp_rw [D.curvatureTensor_eq N.connection N.center]
  rw [hscalar]
  exact neckScale_sq_mul_scalar_center N

theorem neckScale_le_two_mul_of_normalized_scalar_ge (N N' : EpsilonNeck g)
    (hscalar : (1 / 2 : ℝ) ≤ N.scale ^ 2 * N.connection.scalarCurvature N'.center) :
    N'.scale ≤ 2 * N.scale := by
  have hnormal := neckScale_sq_mul_scalar_center_of_connection N' N.connection
  have hmul := mul_le_mul_of_nonneg_left hscalar (sq_nonneg N'.scale)
  have hprod : N'.scale ^ 2 * (N.scale ^ 2 * N.connection.scalarCurvature N'.center) =
      N.scale ^ 2 := by
    calc
      _ = N.scale ^ 2 * (N'.scale ^ 2 * N.connection.scalarCurvature N'.center) := by ring
      _ = N.scale ^ 2 := by rw [hnormal, mul_one]
  rw [hprod] at hmul
  nlinarith [N.scale_pos, N'.scale_pos]

theorem neckScale_le_two_mul_of_normalized_scalar_close (N N' : EpsilonNeck g)
    (hscalar : |N.scale ^ 2 * N.connection.scalarCurvature N'.center - 1| < 1 / 2) :
    N'.scale ≤ 2 * N.scale :=
  neckScale_le_two_mul_of_normalized_scalar_ge N N'
    (by linarith [(abs_lt.mp hscalar).1])

end Scale

theorem exists_nearby_scale_and_containment :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} (N N' : EpsilonNeck g),
        N.epsilon ≤ epsilon₀ →
        N'.center ∈ N.region (-N.epsilon⁻¹ / 2) (N.epsilon⁻¹ / 2) →
        N'.scale ≤ 2 * N.scale ∧ N'.central_sphere ⊆ N.carrier := by
  obtain ⟨epsilon₁, hpos₁, hsmall₁, hscalar⟩ :=
    exists_neck_scalarControl.{u} (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨epsilon₂, hpos₂, _, hcontain⟩ :=
    EpsilonNeck.exists_central_sphere_subset_threshold.{u}
  refine ⟨min epsilon₁ epsilon₂, lt_min hpos₁ hpos₂,
    (min_le_left _ _).trans hsmall₁, ?_⟩
  intro M _ _ _ _ _ _ _ g N N' he hcenter
  have hscale := neckScale_le_two_mul_of_normalized_scalar_close N N'
    (hscalar N (he.trans (min_le_left _ _)) N'.center hcenter.1)
  exact ⟨hscale, hcontain N N' (he.trans (min_le_right _ _)) hscale hcenter⟩

theorem exists_nearby_graphical_sphere :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {epsilon : ℝ},
        0 < epsilon → epsilon ≤ epsilon₀ → ∀ N N' : EpsilonNeck g,
        N.epsilon = epsilon → N'.epsilon = epsilon →
        N'.center ∈ N.region (-epsilon⁻¹ / 2) (epsilon⁻¹ / 2) →
        ∃ h : UnitTwoSphere → ℝ, Continuous h ∧
          (∀ q, h q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) ∧
          N'.central_sphere = range (fun q => N.coordinate_map (q, h q)) := by
  obtain ⟨epsilon₁, hpos₁, hsmall₁, hcontain⟩ := exists_nearby_scale_and_containment.{u}
  obtain ⟨epsilon₂, hpos₂, _, hricci⟩ := EpsilonNeck.exists_ricci_quadratic_control.{u}
  refine ⟨min epsilon₁ epsilon₂, lt_min hpos₁ hpos₂,
    (min_le_left _ _).trans hsmall₁, ?_⟩
  intro M _ _ _ _ _ _ _ g epsilon _ he N N' hN hN' hcenter
  obtain ⟨hscale, hsubset⟩ := hcontain N N'
    (hN ▸ he.trans (min_le_left _ _)) (by simpa only [hN] using hcenter)
  apply N.exists_continuous_centralSphere_graph_of_isLocalHomeomorph N' hsubset
  apply N.centralSphere_projection_isLocalHomeomorph_of_bijective_mfderiv N' hsubset
  intro q
  exact N.centralSphere_projection_mfderiv_bijective_of_ricci_error N.connection N' q
    (hsubset (N'.centralSphere_range ▸ mem_range_self q)) hscale
    (hricci N N.connection (hN ▸ he.trans (min_le_right _ _)))
    (hricci N' N.connection (hN' ▸ he.trans (min_le_right _ _)))

theorem exists_nearby_compact_transport :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {epsilon : ℝ},
        0 < epsilon → epsilon ≤ epsilon₀ → ∀ N N' : EpsilonNeck g,
        N.epsilon = epsilon → N'.epsilon = epsilon →
        N'.center ∈ N.region (-epsilon⁻¹ / 2) (epsilon⁻¹ / 2) →
        ∃ (e : M ≃ₜ M) (K : Set M), IsCompact K ∧ K ⊆ N.carrier ∧
          (∀ x, x ∉ K → e x = x) ∧
          e '' connectedComponent N.center = connectedComponent N'.center ∧
          e '' N.central_sphere = N'.central_sphere := by
  obtain ⟨epsilon₀, hpos, hsmall, hgraph⟩ := exists_nearby_graphical_sphere.{u}
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g epsilon hepos he N N' hN hN' hcenter
  obtain ⟨h, hh, hdom, hsphere⟩ := hgraph hepos he N N' hN hN' hcenter
  obtain ⟨r, hr, hrN, hbound⟩ := N.exists_graph_collar h hh hdom
  refine ⟨N.graphTransport hr hrN h hh hbound, N.closedCollar r,
    N.isCompact_closedCollar hrN, N.closedCollar_subset_carrier hrN,
    fun x hx => N.graphTransport_fixed hr hrN h hh hbound hx, ?_, ?_⟩
  · rw [N.graphTransport_image_connectedComponent]
    exact connectedComponent_eq (N.carrier_subset_connectedComponent hcenter.1)
  · exact (N.graphTransport_image_central_sphere hr hrN h hh hbound).trans hsphere.symm

end PoincareConjecture.M32
