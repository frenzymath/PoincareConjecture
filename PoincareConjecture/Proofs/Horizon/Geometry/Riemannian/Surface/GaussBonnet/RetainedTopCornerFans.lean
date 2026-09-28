import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedBandCoreFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.AmbientSectorAngles

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  (T : RetainedCoordinateTriangulation (M := S))

omit [T2Space S] in
theorem band_internal_top_cut_mem_Ioo
    (p : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs p).count)
    (j k : Fin (T.bands p i).faces.interface.count) (hjk : j.succ = k.castSucc) :
    (T.bands p i).faces.cut j.succ ∈ Ioo (0 : ℝ) 1 := by
  let B := T.bands p i
  constructor
  · rw [← B.faces.cut_first]
    exact B.faces.cut_strictMono (show (0 : Fin (B.faces.interface.count + 1)) < j.succ by
      simp)
  · have h : B.faces.cut k.castSucc < B.faces.cut (Fin.last B.faces.interface.count) := B.faces.cut_strictMono
      (lt_of_lt_of_le (Fin.castSucc_lt_succ (i := k)) (Fin.le_last k.succ))
    exact (congrArg B.faces.cut hjk).trans_lt (h.trans_eq B.faces.cut_last)

omit [T2Space S] in
theorem band_internal_top_point_eq_vertex
    (p : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs p).count)
    (j : Fin (T.bands p i).faces.interface.count) :
    (T.bands p i).ambientTopPoint ((T.bands p i).faces.cut j.succ) =
      (T.bands p i).chartTopVertex j.succ := by
  let B := T.bands p i
  have ht : B.faces.cut j.succ ∈ Icc (B.faces.cut j.castSucc) (B.faces.cut j.succ) :=
    right_mem_Icc.mpr (B.faces.cut_strictMono Fin.castSucc_lt_succ).le
  change ((T.graphs p).piece i).frame.symm
    (B.faces.cuts.coordinates B.faces.open_domain B.faces.smooth_lower
      (B.faces.cut j.succ, B.faces.height (B.faces.cut j.succ))) = _
  rw [B.faces.height_eq_upperGraph ht, (B.faces.upperGraph_endpoints j).2]
  exact B.cut_top_eq_chartTopVertex j j.succ (Or.inr rfl)

theorem collar_germ_at_internal_band_top
    (p : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs p).count)
    (j k : Fin (T.bands p i).faces.interface.count) (hjk : j.succ = k.castSucc) :
    (chartAt Plane (T.chart p.1.1 : S)).symm ⁻¹'
      T.decomposition.fittedRegionCollar T.chart T.cut T.graphs T.chains T.bands
        T.caps T.region p.1.1 =ᶠ[𝓝 ((T.bands p i).chartTopVertex j.succ)]
      (chartAt Plane (T.chart p.1.1 : S)) '' (T.bands p i).faces.carrier := by
  let B := T.bands p i
  let C := (chartAt Plane (T.chart p.1.1 : S)).symm
  have ht := T.band_internal_top_cut_mem_Ioo p i j k hjk
  have hts : B.faces.cut j.succ ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have hpoint := T.band_internal_top_point_eq_vertex p i j
  have hs : B.chartTopVertex j.succ ∈ C.source := by
    rw [← hpoint]
    exact B.ambientTopPoint_mem_source hts
  have hmap : C (B.chartTopVertex j.succ) =
      ((T.graphs p).piece i).strip ((T.chains p).graphCuts i)
        (B.faces.cut j.succ, B.faces.height (B.faces.cut j.succ)) := by
    rw [← hpoint, B.ambientTopPoint_map]
  have hn := T.strip_point_not_mem_endpoint_cuts p i ht
    ⟨(B.faces.height_pos hts).le, le_rfl⟩
  have hb : C (B.chartTopVertex j.succ) ∈ B.faces.carrier := by
    rw [hmap, B.carrier_eq_fixed_strip]
    exact mem_image_of_mem _ ⟨hts, (B.faces.height_pos hts).le, le_rfl⟩
  have hc := T.coordinate_collar_germ_of_band_away_from_endpoint_cuts p i hs hb
    (hmap.symm ▸ hn.1) (hmap.symm ▸ hn.2)
  have himage : C ⁻¹' B.faces.carrier =ᶠ[𝓝 (B.chartTopVertex j.succ)] C.symm '' B.faces.carrier := by
    filter_upwards [C.open_source.mem_nhds hs] with z hz
    apply propext
    change C z ∈ B.faces.carrier ↔ z ∈ C.symm '' B.faces.carrier
    constructor
    · intro h
      exact ⟨C z, h, C.left_inv hz⟩
    · rintro ⟨y, hy, rfl⟩
      have hys := T.chart_source p.1.1 (T.band_regions p i hy)
      simpa only [C.right_inv hys] using hy
  exact hc.trans himage

theorem core_complement_germ_at_internal_band_top
    (p : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs p).count)
    (j k : Fin (T.bands p i).faces.interface.count) (hjk : j.succ = k.castSucc) :
    (T.refined.mesh p.1.1).toPlaneComplex.support =ᶠ[𝓝 ((T.bands p i).chartTopVertex j.succ)]
      (interior ((chartAt Plane (T.chart p.1.1 : S)).symm ⁻¹'
        T.decomposition.fittedRegionCollar T.chart T.cut T.graphs T.chains T.bands
          T.caps T.region p.1.1))ᶜ := by
  let B := T.bands p i
  have ht := T.band_internal_top_cut_mem_Ioo p i j k hjk
  have hts : B.faces.cut j.succ ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have hpoint := T.band_internal_top_point_eq_vertex p i j
  have hs := B.ambientTopPoint_mem_source hts
  have hr := T.band_positive_height_mem_region p i hts (B.faces.height_pos hts) le_rfl
  rw [← hpoint]
  exact T.core_complement_germ_of_mem_region p.1.1 _ hs (by rwa [B.ambientTopPoint_map])

theorem internal_band_top_mem_interior_band_core_union
    (p : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs p).count)
    (j k : Fin (T.bands p i).faces.interface.count) (hjk : j.succ = k.castSucc) :
    (chartAt Plane (T.chart p.1.1 : S)).symm ((T.bands p i).chartTopVertex j.succ) ∈
      interior ((T.bands p i).faces.carrier ∪ (chartAt Plane (T.chart p.1.1 : S)).symm ''
        (T.refined.mesh p.1.1).toPlaneComplex.support) := by
  let B := T.bands p i
  have ht := T.band_internal_top_cut_mem_Ioo p i j k hjk
  have hts : B.faces.cut j.succ ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  rw [← T.band_internal_top_point_eq_vertex p i j, B.ambientTopPoint_map]
  exact mem_interior_iff_mem_nhds.mpr (T.band_core_union_mem_nhds p i ht
    (B.faces.height_pos hts) le_rfl)

omit [T2Space S] in
theorem band_top_functional_mem_scaled_core_contacts
    (p : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs p).count)
    (j : Fin (T.bands p i).faces.interface.count) :
    ∃ l ∈ T.decomposition.fittedCoreRefinementLines T.chart T.cut T.graphs
      T.chains T.bands T.caps T.region p.1.1, ∃ a : ℝ, a ≠ 0 ∧
        (T.bands p i).ambientTopFunctional j = a • l := by
  let B := T.bands p i
  obtain ⟨a, ha, he⟩ := B.ambientTopFunctional_eq_smul_topSupportingLine j
  refine ⟨B.topSupportingLine j, ?_, a, ha, he⟩
  exact T.decomposition.band_line_mem_fittedCoreRefinementLines T.chart T.cut T.graphs
    T.chains T.bands T.caps T.region p i _
      (by simp [B, FiniteChartRegionDecomposition.OrientedGraphPiece.FixedStripBandFaces.coreContactLines,
        List.mem_ofFn])

omit [T2Space S] in
theorem refined_core_monochromatic_band_contacts
    (p : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs p).count)
    (l : Plane →ᵃ[ℝ] ℝ) (hl : l ∈ (T.bands p i).coreContactLines) :
    (T.refined.mesh p.1.1).IsMonochromatic l := by
  rw [T.refined.mesh_eq_refineByLines p.1.1]
  exact (T.coreMeshes p.1.1).refineByLines_isMonochromatic_of_mem _
    (T.decomposition.band_line_mem_fittedCoreRefinementLines T.chart T.cut T.graphs
      T.chains T.bands T.caps T.region p i l hl)

theorem core_germ_at_internal_band_top_of_band_germ
    (p : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs p).count)
    (j k : Fin (T.bands p i).faces.interface.count) (hjk : j.succ = k.castSucc)
    (A : Set Plane)
    (hband : (chartAt Plane (T.chart p.1.1 : S)) '' (T.bands p i).faces.carrier
      =ᶠ[𝓝 ((T.bands p i).chartTopVertex j.succ)] A) :
    (T.refined.mesh p.1.1).toPlaneComplex.support
      =ᶠ[𝓝 ((T.bands p i).chartTopVertex j.succ)] (interior A)ᶜ := by
  have hc := T.core_complement_germ_at_internal_band_top p i j k hjk
  have hi := support_eventuallyEq_interior
    ((T.collar_germ_at_internal_band_top p i j k hjk).trans hband)
  filter_upwards [hc, hi] with z hcz hiz
  change (T.refined.mesh p.1.1).toPlaneComplex.support z = ¬interior A z
  change (T.refined.mesh p.1.1).toPlaneComplex.support z = ¬interior _ z at hcz
  rwa [hiz] at hcz

set_option maxHeartbeats 1600000 in

theorem vertex_fan_at_convex_internal_band_top
    (g : RiemannianMetric 2 S) (p : T.decomposition.IncidentEdgeIndex)
    (i : Fin (T.graphs p).count)
    (j k : Fin (T.bands p i).faces.interface.count) (hjk : j.succ = k.castSucc)
    (hslope : ((T.bands p i).faces.interface.piece k).linear 1 <
      ((T.bands p i).faces.interface.piece j).linear 1) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis
      ((chartAt Plane (T.chart p.1.1 : S)).symm ((T.bands p i).chartTopVertex j.succ)) =
        2 * Real.pi := by
  let B := T.bands p i
  let C := (chartAt Plane (T.chart p.1.1 : S)).symm
  obtain ⟨c, hc0, hc1, hc2, _, _, hband⟩ := B.exists_ambient_internal_top_convex_sector_coordinates
    (T.refined.mesh p.1.1) (T.refined_core_monochromatic_band_contacts p i) j k hjk hslope
  have hlocal := T.core_germ_at_internal_band_top_of_band_germ p i j k hjk _ hband
  rw [← hc0] at hlocal
  have hmem : c 0 ∈ (T.refined.mesh p.1.1).toPlaneComplex.support := by
    apply (propext_iff.mp hlocal.eq_of_nhds).mpr
    rw [compl_interior_convexSector]
    change c.coord 1 (c 0) ≤ 0 ∨ c.coord 2 (c 0) ≤ 0
    simp
  have hcontact (l : Fin B.faces.interface.count) :
      ∃ m ∈ T.decomposition.fittedCoreRefinementLines T.chart T.cut T.graphs
        T.chains T.bands T.caps T.region p.1.1, ∃ a : ℝ, a ≠ 0 ∧
          -B.ambientTopFunctional l = a • m := by
    obtain ⟨m, hm, a, ha, he⟩ := T.band_top_functional_mem_scaled_core_contacts p i l
    exact ⟨m, hm, -a, neg_ne_zero.mpr ha, by rw [he, neg_smul]⟩
  have hcore := T.core_contribution_at_reflex_sector g p.1.1 c
    (hc1 ▸ hcontact j) (hc2 ▸ hcontact k) hmem hlocal
  have hbandangle := B.internal_top_refined_vertex_fan_eq_convex_sector g
    (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞))
    (contMDiffOn_chart (I := 𝓡 2) (n := ∞))
    (fun a => (T.refinement.subdivision (.inr (.inl ⟨⟨p, i⟩, a⟩))).refinement_lines)
    j k hjk hslope c hc0 hc1 hc2
  have heq (a : Fin B.faces.interface.count × Bool) :
      T.refinement.mesh (.inr (.inl ⟨⟨p, i⟩, a⟩)) =
        (TriangleMesh.single (B.faces.faceBasis a) (B.faces.faceBasis a).ind).refineByLines
          (T.refinement.subdivision (.inr (.inl ⟨⟨p, i⟩, a⟩))).refinement_lines :=
    (T.refinement.subdivision (.inr (.inl ⟨⟨p, i⟩, a⟩))).mesh_eq_refineByLines
  have hwhole := T.vertex_contribution_eq_band_add_core g p i
    (T.internal_band_top_mem_interior_band_core_union p i j k hjk)
  rw [← hc0] at hwhole ⊢
  simp_rw [heq] at hwhole
  rw [hbandangle, hcore] at hwhole
  linarith

set_option maxHeartbeats 1600000 in

theorem vertex_fan_at_reflex_internal_band_top
    (g : RiemannianMetric 2 S) (p : T.decomposition.IncidentEdgeIndex)
    (i : Fin (T.graphs p).count)
    (j k : Fin (T.bands p i).faces.interface.count) (hjk : j.succ = k.castSucc)
    (hslope : ((T.bands p i).faces.interface.piece j).linear 1 <
      ((T.bands p i).faces.interface.piece k).linear 1) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis
      ((chartAt Plane (T.chart p.1.1 : S)).symm ((T.bands p i).chartTopVertex j.succ)) =
        2 * Real.pi := by
  let B := T.bands p i
  obtain ⟨c, hc0, hc1, hc2, _, _, hband⟩ := B.exists_ambient_internal_top_reflex_sector_coordinates
    (T.refined.mesh p.1.1) (T.refined_core_monochromatic_band_contacts p i) j k hjk hslope
  have hlocal := T.core_germ_at_internal_band_top_of_band_germ p i j k hjk _ hband
  rw [← hc0, compl_interior_reflexSector] at hlocal
  have hmem : c 0 ∈ (T.refined.mesh p.1.1).toPlaneComplex.support := by
    apply (propext_iff.mp hlocal.eq_of_nhds).mpr
    change 0 ≤ c.coord 1 (c 0) ∧ 0 ≤ c.coord 2 (c 0)
    simp
  have hcore := T.core_contribution_at_convex_sector g p.1.1 c
    (hc1 ▸ T.band_top_functional_mem_scaled_core_contacts p i j)
    (hc2 ▸ T.band_top_functional_mem_scaled_core_contacts p i k) hmem hlocal
  have hbandangle := B.internal_top_refined_vertex_fan_eq_reflex_sector g
    (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞))
    (contMDiffOn_chart (I := 𝓡 2) (n := ∞))
    (fun a => (T.refinement.subdivision (.inr (.inl ⟨⟨p, i⟩, a⟩))).refinement_lines)
    j k hjk hslope c hc0 hc1 hc2
  have heq (a : Fin B.faces.interface.count × Bool) :
      T.refinement.mesh (.inr (.inl ⟨⟨p, i⟩, a⟩)) =
        (TriangleMesh.single (B.faces.faceBasis a) (B.faces.faceBasis a).ind).refineByLines
          (T.refinement.subdivision (.inr (.inl ⟨⟨p, i⟩, a⟩))).refinement_lines :=
    (T.refinement.subdivision (.inr (.inl ⟨⟨p, i⟩, a⟩))).mesh_eq_refineByLines
  have hwhole := T.vertex_contribution_eq_band_add_core g p i
    (T.internal_band_top_mem_interior_band_core_union p i j k hjk)
  rw [← hc0] at hwhole ⊢
  simp_rw [heq] at hwhole
  rw [hbandangle, hcore] at hwhole
  linarith

set_option maxHeartbeats 1600000 in

theorem canonical_vertex_fan_at_straight_internal_band_top
    (g : RiemannianMetric 2 S) (p : T.decomposition.IncidentEdgeIndex)
    (i : Fin (T.graphs p).count)
    (j k : Fin (T.bands p i).faces.interface.count) (hjk : j.succ = k.castSucc)
    (hslope : ((T.bands p i).faces.interface.piece j).linear 1 =
      ((T.bands p i).faces.interface.piece k).linear 1)
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    (hq : q.1 = (chartAt Plane (T.chart p.1.1 : S)).symm ((T.bands p i).chartTopVertex j.succ)) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis q.1 =
      2 * Real.pi := by
  let B := T.bands p i
  have hband := B.ambient_carrier_internal_top_halfspace_of_slope_eq j k hjk hslope
  have hlocal := T.core_germ_at_internal_band_top_of_band_germ p i j k hjk _ hband
  rw [interior_affine_halfspace_nonpos _ (B.ambientTopFunctional_surjective j)] at hlocal
  have hlocal' : (T.refined.mesh p.1.1).toPlaneComplex.support =ᶠ[𝓝 (B.chartTopVertex j.succ)]
      {z | 0 ≤ B.ambientTopFunctional j z} := by
    filter_upwards [hlocal] with z hz
    apply propext
    have he : z ∈ (T.refined.mesh p.1.1).toPlaneComplex.support ↔
        ¬B.ambientTopFunctional j z < 0 := propext_iff.mp hz
    exact he.trans not_lt
  have hzero := B.ambientTopFunctional_right_vertex j
  have hmem : B.chartTopVertex j.succ ∈ (T.refined.mesh p.1.1).toPlaneComplex.support := by
    apply (propext_iff.mp hlocal'.eq_of_nhds).mpr
    change 0 ≤ B.ambientTopFunctional j (B.chartTopVertex j.succ)
    rw [hzero]
  have hcore := T.core_contribution_at_straight_canonical_vertex g p.1.1 q hq.symm hmem
    (B.ambientTopFunctional j) (B.ambientTopFunctional_surjective j)
    (T.band_top_functional_mem_scaled_core_contacts p i j) hzero hlocal'
  have hbandangle := B.internal_top_refined_vertex_fan_eq_pi_of_slope_eq g
    (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞))
    (contMDiffOn_chart (I := 𝓡 2) (n := ∞))
    (fun a => (T.refinement.subdivision (.inr (.inl ⟨⟨p, i⟩, a⟩))).refinement_lines)
    j k hjk hslope
  have heq (a : Fin B.faces.interface.count × Bool) :
      T.refinement.mesh (.inr (.inl ⟨⟨p, i⟩, a⟩)) =
        (TriangleMesh.single (B.faces.faceBasis a) (B.faces.faceBasis a).ind).refineByLines
          (T.refinement.subdivision (.inr (.inl ⟨⟨p, i⟩, a⟩))).refinement_lines :=
    (T.refinement.subdivision (.inr (.inl ⟨⟨p, i⟩, a⟩))).mesh_eq_refineByLines
  have hwhole := T.vertex_contribution_eq_band_add_core g p i
    (T.internal_band_top_mem_interior_band_core_union p i j k hjk)
  rw [← hq] at hwhole hbandangle
  simp_rw [heq] at hwhole
  rw [hbandangle, hcore] at hwhole
  linarith

set_option maxHeartbeats 1600000 in

theorem canonical_vertex_fan_at_internal_band_top
    (g : RiemannianMetric 2 S) (p : T.decomposition.IncidentEdgeIndex)
    (i : Fin (T.graphs p).count)
    (j k : Fin (T.bands p i).faces.interface.count) (hjk : j.succ = k.castSucc)
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    (hq : q.1 = (chartAt Plane (T.chart p.1.1 : S)).symm ((T.bands p i).chartTopVertex j.succ)) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis q.1 =
      2 * Real.pi := by
  rcases lt_trichotomy (((T.bands p i).faces.interface.piece j).linear 1)
      (((T.bands p i).faces.interface.piece k).linear 1) with h | h | h
  · rw [hq]
    exact T.vertex_fan_at_reflex_internal_band_top g p i j k hjk h
  · exact T.canonical_vertex_fan_at_straight_internal_band_top g p i j k hjk h q hq
  · rw [hq]
    exact T.vertex_fan_at_convex_internal_band_top g p i j k hjk h

end PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation
