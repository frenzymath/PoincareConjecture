import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedBandCoreFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedTopCornerFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.PointClassification







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

set_option maxHeartbeats 800000 in
omit [T2Space S] in


theorem band_contribution_at_open_top_canonical_vertex
    (g : RiemannianMetric 2 S) (p : T.decomposition.IncidentEdgeIndex)
    (i : Fin (T.graphs p).count) (j : Fin (T.bands p i).faces.interface.count)
    {t : ℝ} (ht : t ∈ Ioo ((T.bands p i).faces.cut j.castSucc) ((T.bands p i).faces.cut j.succ))
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    (hq : q.1 = ((T.graphs p).piece i).strip ((T.chains p).graphCuts i)
      (t, (T.bands p i).faces.height t)) :
    (∑ a : Fin (T.bands p i).faces.interface.count × Bool,
      meshVertexAngleContribution g ((T.bands p i).faces.faceCoordinates a)
        (T.refinement.mesh (.inr (.inl ⟨⟨p, i⟩, a⟩))) q.1) = Real.pi := by
  let B := T.bands p i
  have hts : t ∈ Icc (0 : ℝ) 1 := by
    rw [← B.faces.cut_interval_cover]
    exact mem_iUnion.mpr ⟨j, ht.1.le, ht.2.le⟩
  have hpoint : B.faces.coordinates (collarParameterEquiv.symm (t, B.faces.height t)) = q.1 :=
    (B.coordinates_eq _).trans hq.symm
  have hband : q.1 ∈ B.faces.carrier := by
    rw [hq, B.carrier_eq_fixed_strip]
    exact mem_image_of_mem _ ⟨hts, (B.faces.height_pos hts).le, le_rfl⟩
  have hface : ∃ a : Fin B.faces.interface.count × Bool, q.1 ∈ (B.faces.face a).carrier :=
    mem_iUnion.mp hband
  obtain ⟨a, ha⟩ := hface
  have hused : ∃ (u : (T.refinement.mesh (.inr (.inl ⟨⟨p, i⟩, a⟩))).Triangle)
      (v : (T.refinement.mesh (.inr (.inl ⟨⟨p, i⟩, a⟩))).Vertex),
      v ∈ u.1 ∧ B.faces.faceCoordinates a
        ((T.refinement.mesh (.inr (.inl ⟨⟨p, i⟩, a⟩))).position v) = q.1 :=
    T.parent_mesh_vertex_is_used q (.inr (.inl ⟨⟨p, i⟩, a⟩)) (by
    change q.1 ∈ B.faces.faceCoordinates a ''
      (T.refinement.mesh (.inr (.inl ⟨⟨p, i⟩, a⟩))).toPlaneComplex.support
    rw [(T.refinement.subdivision (.inr (.inl ⟨⟨p, i⟩, a⟩))).support]
    exact B.faces.face_carrier_eq_coordinates a ▸ ha)
  have heq (a : Fin B.faces.interface.count × Bool) :
      T.refinement.mesh (.inr (.inl ⟨⟨p, i⟩, a⟩)) =
        (TriangleMesh.single (B.faces.faceBasis a) (B.faces.faceBasis a).ind).refineByLines
          (T.refinement.subdivision (.inr (.inl ⟨⟨p, i⟩, a⟩))).refinement_lines :=
    (T.refinement.subdivision (.inr (.inl ⟨⟨p, i⟩, a⟩))).mesh_eq_refineByLines
  have hc := linearGraphCoordinates_contMDiff
    (chartAt Plane (T.chart p.1.1 : S)).symm ((T.graphs p).piece i).frame
    (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞))
    (contMDiffOn_chart (I := 𝓡 2) (n := ∞))
  exact B.faces.upper_graph_actual_mesh_vertex_fan g hc.1 hc.2
    (fun a => T.refinement.mesh (.inr (.inl ⟨⟨p, i⟩, a⟩)))
    (fun a => (T.refinement.subdivision (.inr (.inl ⟨⟨p, i⟩, a⟩))).refinement_lines)
    heq j hts ht q.1 hpoint ⟨a, hused⟩



theorem core_contribution_at_open_top_canonical_vertex
    (g : RiemannianMetric 2 S) (p : T.decomposition.IncidentEdgeIndex)
    (i : Fin (T.graphs p).count) (j : Fin (T.bands p i).faces.interface.count)
    {t : ℝ} (ht : t ∈ Ioo ((T.bands p i).faces.cut j.castSucc) ((T.bands p i).faces.cut j.succ))
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    (hq : q.1 = ((T.graphs p).piece i).strip ((T.chains p).graphCuts i)
      (t, (T.bands p i).faces.height t)) :
    (∑ u : (T.refined.mesh p.1.1).Triangle,
      meshVertexAngleContribution g (chartAt Plane (T.chart p.1.1 : S)).symm
        (T.refinement.mesh (.inr (.inr ⟨p.1.1, u⟩))) q.1) = Real.pi := by
  let B := T.bands p i
  have hlocal := T.core_halfspace_at_open_band_top p i j ht
  have hzero := B.ambientTopFunctional_topPoint j ⟨ht.1.le, ht.2.le⟩
  have hmem : B.ambientTopPoint t ∈ (T.refined.mesh p.1.1).toPlaneComplex.support := by
    apply (propext_iff.mp hlocal.eq_of_nhds).mpr
    change 0 ≤ B.ambientTopFunctional j (B.ambientTopPoint t)
    rw [hzero]
  apply T.core_contribution_at_straight_canonical_vertex g p.1.1 q
    ((B.ambientTopPoint_map t).trans hq.symm) hmem (B.ambientTopFunctional j)
    (B.ambientTopFunctional_surjective j) _ hzero hlocal
  obtain ⟨r, hr, he⟩ := B.ambientTopFunctional_eq_smul_topSupportingLine j
  refine ⟨B.topSupportingLine j, ?_, r, hr, he⟩
  apply T.decomposition.band_line_mem_fittedCoreRefinementLines
    T.chart T.cut T.graphs T.chains T.bands T.caps T.region p i
  change B.topSupportingLine j ∈ B.coreContactLines
  simp [FiniteChartRegionDecomposition.OrientedGraphPiece.FixedStripBandFaces.coreContactLines,
    List.mem_ofFn]



theorem canonical_vertex_fan_on_open_band_top
    (g : RiemannianMetric 2 S) (p : T.decomposition.IncidentEdgeIndex)
    (i : Fin (T.graphs p).count) (j : Fin (T.bands p i).faces.interface.count)
    {t : ℝ} (ht : t ∈ Ioo ((T.bands p i).faces.cut j.castSucc) ((T.bands p i).faces.cut j.succ))
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    (hq : q.1 = ((T.graphs p).piece i).strip ((T.chains p).graphCuts i)
      (t, (T.bands p i).faces.height t)) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis q.1 =
      2 * Real.pi := by
  let B := T.bands p i
  have hti : t ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · have h := B.faces.cut_strictMono.monotone (Fin.zero_le j.castSucc)
      rw [B.faces.cut_first] at h
      exact h.trans_lt ht.1
    · have h := B.faces.cut_strictMono.monotone (Fin.le_last j.succ)
      rw [B.faces.cut_last] at h
      exact ht.2.trans_le h
  have hint := mem_interior_iff_mem_nhds.mpr (T.band_core_union_mem_nhds p i hti
    (B.faces.height_pos ⟨hti.1.le, hti.2.le⟩) le_rfl)
  rw [← hq] at hint
  rw [T.vertex_contribution_eq_band_add_core g p i hint,
    T.band_contribution_at_open_top_canonical_vertex g p i j ht q hq,
    T.core_contribution_at_open_top_canonical_vertex g p i j ht q hq]
  ring

set_option maxHeartbeats 800000 in


theorem canonical_vertex_fan_on_interior_band_top
    (g : RiemannianMetric 2 S) (p : T.decomposition.IncidentEdgeIndex)
    (i : Fin (T.graphs p).count) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    (hq : q.1 = ((T.graphs p).piece i).strip ((T.chains p).graphCuts i)
      (t, (T.bands p i).faces.height t)) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis q.1 =
      2 * Real.pi := by
  rcases (T.bands p i).faces.interior_parameter_cell_cases ht with
    ⟨j, hj⟩ | ⟨j, k, hjk, htj⟩
  · exact T.canonical_vertex_fan_on_open_band_top g p i j hj q hq
  · apply T.canonical_vertex_fan_at_internal_band_top g p i j k hjk q
    rw [hq, htj, ← T.band_internal_top_point_eq_vertex p i j,
      (T.bands p i).ambientTopPoint_map]

end PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation
