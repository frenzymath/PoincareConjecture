import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedCapCoreFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedBandCutFans

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes Poincare.Topology.Plane.Triangles

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  (T : RetainedCoordinateTriangulation (M := S))

theorem vertex_contribution_eq_cap_add_band
    (g : RiemannianMetric 2 S) (p : T.decomposition.vertices) (s : Bool × Bool)
    (a : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs a).count)
    {q : S} (hq : q ∈ interior (((T.caps p).face s).carrier ∪ (T.bands a i).faces.carrier)) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis q =
      meshVertexAngleContribution g ((T.caps p).coordinates s)
        (T.refinement.mesh (.inl (p, s))) q +
      ∑ j : Fin (T.bands a i).faces.interface.count × Bool,
        meshVertexAngleContribution g ((T.bands a i).faces.faceCoordinates j)
          (T.refinement.mesh (.inr (.inl ⟨⟨a, i⟩, j⟩))) q := by
  rw [T.vertex_contribution_eq_parent_sum]
  have h := mesh_family_contribution_eq_two_subfamily_sums g T.refinement.mesh
    T.parentCoordinates T.refinement.face (T.refinement.mesh_source T.parent_source)
    T.refinement.carrier_eq T.refinement.intersection_frontier
    (fun _ : Unit => (.inl (p, s) : T.Parent))
    (fun j : Fin (T.bands a i).faces.interface.count × Bool =>
      (.inr (.inl ⟨⟨a, i⟩, j⟩) : T.Parent))
    (fun _ _ _ => Subsingleton.elim _ _) (by intro j k h; simpa using h)
    (by intro j k h; cases h) (q := q) ?_
  · simp only [Fintype.sum_unique] at h
    change (∑ j, meshVertexAngleContribution g (T.parentCoordinates j)
      (T.refinement.mesh j) q) =
      meshVertexAngleContribution g ((T.caps p).coordinates s)
        (T.refinement.mesh (.inl (p, s))) q +
      ∑ j : Fin (T.bands a i).faces.interface.count × Bool,
        meshVertexAngleContribution g ((T.bands a i).faces.faceCoordinates j)
          (T.refinement.mesh (.inr (.inl ⟨⟨a, i⟩, j⟩))) q at h
    exact h
  · rw [T.band_parent_support_union]
    rw [iUnion_const, (T.refinement.subdivision (.inl (p, s))).support]
    change q ∈ interior (((T.caps p).coordinates s ''
      convexHull ℝ (range (rightTriangleBasis (T.caps p).scale_pos))) ∪ _)
    rwa [← (T.caps p).carrier_eq s]

theorem canonical_vertex_fan_on_open_cap_band_edge
    (g : RiemannianMetric 2 S) (p : T.decomposition.vertices) (s : Bool × Bool)
    (a : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs a).count)
    (right : Bool) {t u : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1)
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    (hcap : (((T.caps p).face s).boundary 0).map t = q.1)
    (hband : ((T.bands a i).faces.endpointEdge right).map u = q.1)
    (hshared : ((T.bands a i).faces.endpointEdge right).map '' Icc (0 : ℝ) 1 ⊆
      (((T.caps p).face s).boundary 0).map '' Icc (0 : ℝ) 1) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis q.1 =
      2 * Real.pi := by
  have hint := (T.caps p).mem_interior_union_band (T.bands a i).faces s right ht hu
    (hcap.trans hband.symm) hshared ((T.cap_disjoint_band_interior p s a i).mono_left interior_subset)
  rw [hcap] at hint
  rw [T.vertex_contribution_eq_cap_add_band g p s a i hint,
    T.cap_contribution_at_open_chord_canonical_vertex g p s ht q hcap,
    T.band_open_endpoint_contribution g a i q right hu hband]
  ring

omit [T2Space S] in

theorem open_left_attachment_subset_endpointEdge (a : T.decomposition.IncidentEdgeIndex) :
    (T.leftCap a).openChordSegment T.length ⊆
      ((T.bands a (T.graphs a).firstPiece).faces.endpointEdge false).map '' Ioo (0 : ℝ) 1 := by
  simpa only [Prod.eta, ContinuousLinearEquiv.symm_apply_apply,
    OpenPartialHomeomorph.symm_symm, (T.graphs a).firstPiece_castSucc,
    (T.graphs a).cut_first, (T.chains a).first,
    FiniteChartRegionDecomposition.CapGraphEndpoint.openChordSegment,
    FiniteChartRegionDecomposition.edgeFromEndpoint, Bool.false_eq_true, ite_false] using
    (T.bands a (T.graphs a).firstPiece).open_left_ray_subset_endpointEdge
      ((T.graphs a).cut_lt (T.graphs a).firstPiece).le

omit [T2Space S] in

theorem open_right_attachment_subset_endpointEdge (a : T.decomposition.IncidentEdgeIndex) :
    (T.rightCap a).openChordSegment T.length ⊆
      ((T.bands a (T.graphs a).lastPiece).faces.endpointEdge true).map '' Ioo (0 : ℝ) 1 := by
  simpa only [Prod.eta, ContinuousLinearEquiv.symm_apply_apply,
    OpenPartialHomeomorph.symm_symm, (T.graphs a).lastPiece_succ,
    (T.graphs a).cut_last, (T.chains a).last,
    FiniteChartRegionDecomposition.CapGraphEndpoint.openChordSegment,
    FiniteChartRegionDecomposition.edgeFromEndpoint, ite_true] using
    (T.bands a (T.graphs a).lastPiece).open_right_ray_subset_endpointEdge
      ((T.graphs a).cut_lt (T.graphs a).lastPiece).le

theorem canonical_vertex_fan_on_open_left_attachment
    (g : RiemannianMetric 2 S) (a : T.decomposition.IncidentEdgeIndex)
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    (hq : q.1 ∈ (T.leftCap a).openChordSegment T.length) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis q.1 =
      2 * Real.pi := by
  obtain ⟨t, ht, htq⟩ := (T.leftCap a).openChordSegment_subset_open_chord T.length_le_one hq
  obtain ⟨u, hu, huq⟩ := T.open_left_attachment_subset_endpointEdge a hq
  apply T.canonical_vertex_fan_on_open_cap_band_edge g
    (T.decomposition.edgeEndpoint a.1.2 false) (T.leftCap a).sector
    a (T.graphs a).firstPiece false ht hu q htq huq
  rw [(T.bands a (T.graphs a).firstPiece).faces.endpointEdge_image]
  simpa only [Bool.false_eq_true, ite_false, T.first_band_leftCut_eq_chordSegment] using
    (T.leftCap a).chordSegment_subset_chord T.length_le_one

theorem canonical_vertex_fan_on_open_right_attachment
    (g : RiemannianMetric 2 S) (a : T.decomposition.IncidentEdgeIndex)
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    (hq : q.1 ∈ (T.rightCap a).openChordSegment T.length) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis q.1 =
      2 * Real.pi := by
  obtain ⟨t, ht, htq⟩ := (T.rightCap a).openChordSegment_subset_open_chord T.length_le_one hq
  obtain ⟨u, hu, huq⟩ := T.open_right_attachment_subset_endpointEdge a hq
  apply T.canonical_vertex_fan_on_open_cap_band_edge g
    (T.decomposition.edgeEndpoint a.1.2 true) (T.rightCap a).sector
    a (T.graphs a).lastPiece true ht hu q htq huq
  rw [(T.bands a (T.graphs a).lastPiece).faces.endpointEdge_image]
  simpa only [ite_true, T.last_band_rightCut_eq_chordSegment] using
    (T.rightCap a).chordSegment_subset_chord T.length_le_one

end PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation
