import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedBandInteriorFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.OpenEndpointFans
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.CutGluing
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.MeshSubfamilyContribution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open Set
open scoped Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  (T : RetainedCoordinateTriangulation (M := S))

theorem band_open_endpoint_contribution (g : RiemannianMetric 2 S)
    (p : T.decomposition.IncidentEdgeIndex) (i : Fin (T.graphs p).count)
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    (right : Bool) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hpoint : ((T.bands p i).faces.endpointEdge right).map t = q.1) :
    (∑ s : Fin (T.bands p i).faces.interface.count × Bool,
      meshVertexAngleContribution g ((T.bands p i).faces.faceCoordinates s)
        (T.refinement.mesh (.inr (.inl ⟨⟨p, i⟩, s⟩))) q.1) = Real.pi := by
  have heq (s : Fin (T.bands p i).faces.interface.count × Bool) :
      T.refinement.mesh (.inr (.inl ⟨⟨p, i⟩, s⟩)) =
        (TriangleMesh.single ((T.bands p i).faces.faceBasis s)
          ((T.bands p i).faces.faceBasis s).ind).refineByLines
            (T.refinement.subdivision (.inr (.inl ⟨⟨p, i⟩, s⟩))).refinement_lines :=
    (T.refinement.subdivision (.inr (.inl ⟨⟨p, i⟩, s⟩))).mesh_eq_refineByLines
  have hcoord := linearGraphCoordinates_contMDiff
    (chartAt Plane (T.chart p.1.1 : S)).symm ((T.graphs p).piece i).frame
    (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞)) (contMDiffOn_chart (I := 𝓡 2) (n := ∞))
  have hfan := (T.bands p i).faces.open_endpoint_refined_vertex_fan g hcoord.1 hcoord.2
    (fun s => (T.refinement.subdivision (.inr (.inl ⟨⟨p, i⟩, s⟩))).refinement_lines) right ht
  have hused (s : Fin (T.bands p i).faces.interface.count × Bool)
      (hs : ((T.bands p i).faces.endpointEdge right).map t ∈ ((T.bands p i).faces.face s).carrier) :
      ∃ (u : (T.refinement.mesh (.inr (.inl ⟨⟨p, i⟩, s⟩))).Triangle)
        (v : (T.refinement.mesh (.inr (.inl ⟨⟨p, i⟩, s⟩))).Vertex),
        v ∈ u.1 ∧ (T.bands p i).faces.faceCoordinates s
          ((T.refinement.mesh (.inr (.inl ⟨⟨p, i⟩, s⟩))).position v) =
            ((T.bands p i).faces.endpointEdge right).map t := by
    have hw := T.parent_mesh_vertex_is_used q (.inr (.inl ⟨⟨p, i⟩, s⟩)) (by
      change q.1 ∈ (T.bands p i).faces.faceCoordinates s ''
        (T.refinement.mesh (.inr (.inl ⟨⟨p, i⟩, s⟩))).toPlaneComplex.support
      rw [(T.refinement.subdivision (.inr (.inl ⟨⟨p, i⟩, s⟩))).support]
      exact (T.bands p i).faces.face_carrier_eq_coordinates s ▸ (hpoint ▸ hs))
    obtain ⟨u, v, hv, he⟩ := hw
    exact ⟨u, v, hv, he.trans hpoint.symm⟩
  have hresult := hfan (fun s hs => by
    have hw := hused s hs
    rw [heq s] at hw
    exact hw)
  simpa only [← heq, hpoint] using hresult

theorem vertex_contribution_eq_two_band_sum_of_interior
    (g : RiemannianMetric 2 S) (p : T.decomposition.IncidentEdgeIndex)
    (i j : Fin (T.graphs p).count) (hne : i ≠ j) {q : S}
    (hq : q ∈ interior ((T.bands p i).faces.carrier ∪ (T.bands p j).faces.carrier)) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis q =
      (∑ s : Fin (T.bands p i).faces.interface.count × Bool,
        meshVertexAngleContribution g ((T.bands p i).faces.faceCoordinates s)
          (T.refinement.mesh (.inr (.inl ⟨⟨p, i⟩, s⟩))) q) +
      (∑ s : Fin (T.bands p j).faces.interface.count × Bool,
        meshVertexAngleContribution g ((T.bands p j).faces.faceCoordinates s)
          (T.refinement.mesh (.inr (.inl ⟨⟨p, j⟩, s⟩))) q) := by
  rw [T.vertex_contribution_eq_parent_sum]
  apply mesh_family_contribution_eq_two_subfamily_sums g T.refinement.mesh T.parentCoordinates
    T.refinement.face (T.refinement.mesh_source T.parent_source) T.refinement.carrier_eq
    T.refinement.intersection_frontier
    (fun s : Fin (T.bands p i).faces.interface.count × Bool => (.inr (.inl ⟨⟨p, i⟩, s⟩) : T.Parent))
    (fun s : Fin (T.bands p j).faces.interface.count × Bool => (.inr (.inl ⟨⟨p, j⟩, s⟩) : T.Parent))
  · intro a b h
    simpa using h
  · intro a b h
    simpa using h
  · intro a b h
    have hs := congrArg Sigma.fst (Sum.inl.inj (Sum.inr.inj h))
    have hij : i = j := by simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hs
    exact hne hij
  · rwa [T.band_parent_support_union p i, T.band_parent_support_union p j]

theorem canonical_vertex_fan_on_open_band_cut
    (g : RiemannianMetric 2 S) (p : T.decomposition.IncidentEdgeIndex)
    (i j : Fin (T.graphs p).count) (hij : i.succ = j.castSucc)
    (q : Euler.CoordinateVertex T.refinement.coordinates T.refinement.basis)
    (hq : q.1 ∈ (T.chains p).cutRay i.succ '' Ioo (0 : ℝ) T.length) :
    coordinateVertexAngleContribution g T.refinement.coordinates T.refinement.basis q.1 =
      2 * Real.pi := by
  have hne : i ≠ j := by
    intro he
    have hv := congrArg Fin.val hij
    rw [he] at hv
    simp only [Fin.val_succ, Fin.val_castSucc] at hv
    omega
  have hint := (T.chains p).open_cutRay_subset_interior_adjacent_union
    (T.bands p) i j hij (T.strip_adjacent p i j hij) hq
  rw [T.vertex_contribution_eq_two_band_sum_of_interior g p i j hne hint]
  have hleft : q.1 ∈ ((T.bands p i).faces.endpointEdge true).map '' Ioo (0 : ℝ) 1 := by
    apply (T.bands p i).open_right_ray_subset_endpointEdge ((T.graphs p).cut_lt i).le
    simpa only [FiniteChartRegionDecomposition.OrientedEdgeGraphSubdivision.CutChain.cutRay,
      Prod.eta, ContinuousLinearEquiv.symm_apply_apply] using hq
  have hright : q.1 ∈ ((T.bands p j).faces.endpointEdge false).map '' Ioo (0 : ℝ) 1 := by
    apply (T.bands p j).open_left_ray_subset_endpointEdge ((T.graphs p).cut_lt j).le
    simpa only [FiniteChartRegionDecomposition.OrientedEdgeGraphSubdivision.CutChain.cutRay,
      Prod.eta, ContinuousLinearEquiv.symm_apply_apply, hij] using hq
  obtain ⟨s, hs, hsq⟩ := hleft
  obtain ⟨t, ht, htq⟩ := hright
  rw [T.band_open_endpoint_contribution g p i q true hs hsq,
    T.band_open_endpoint_contribution g p j q false ht htq]
  ring

end PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation
