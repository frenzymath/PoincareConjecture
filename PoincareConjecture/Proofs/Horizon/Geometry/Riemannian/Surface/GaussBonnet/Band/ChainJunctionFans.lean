import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.CapBandRadialRays
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.EndpointFans
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.CutGluing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Classical
open scoped Manifold ContDiff Bundle Topology Matrix
open Poincare.Topology.Plane.Meshes Poincare.Topology.Plane.Triangles
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition.OrientedEdgeGraphSubdivision.CutChain

universe u
variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {D : FiniteChartRegionDecomposition (M := M)} {e : D.EdgeIndex} {R : D.regions}
  {C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M} {a b : ℝ}
  {S : D.OrientedEdgeGraphSubdivision e R C a b}
  {dLeft dRight : EuclideanSpace ℝ (Fin 2)} (K : S.CutChain dLeft dRight)
  {δ r : ℝ}
  (B : ∀ i : Fin S.count, (S.piece i).FixedStripBandFaces (K.graphCuts i) δ r r)

theorem adjacent_cut_velocity_pos_smul
    (hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source)
    (hCinv : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target)
    (i j : Fin S.count) (hij : i.succ = j.castSucc) :
    ∃ c : ℝ, 0 < c ∧
      coordinateTriangleVelocity ((B j).faces.faceCoordinates ((B j).faces.firstCell, true))
          ((B j).faces.faceBasis ((B j).faces.firstCell, true)) 0 1 = c •
        coordinateTriangleVelocity ((B i).faces.faceCoordinates ((B i).faces.lastCell, false))
          ((B i).faces.faceBasis ((B i).faces.lastCell, false)) 1 2 := by
  have hFi := linearGraphCoordinates_contMDiff C (S.piece i).frame hC hCinv
  have hFj := linearGraphCoordinates_contMDiff C (S.piece j).frame hC hCinv
  apply coordinateTriangleVelocity_pos_smul_of_image_eq
    ((B i).faces.faceCoordinates ((B i).faces.lastCell, false))
    ((B j).faces.faceCoordinates ((B j).faces.firstCell, true))
    ((B i).faces.faceBasis ((B i).faces.lastCell, false))
    ((B j).faces.faceBasis ((B j).faces.firstCell, true))
    ((B i).faces.smooth_faceCoordinates hFi.1 _) ((B i).faces.smooth_faceCoordinates_symm hFi.2 _)
    ((B j).faces.smooth_faceCoordinates hFj.1 _) ((B j).faces.smooth_faceCoordinates_symm hFj.2 _)
    ((B i).faces.face_triangle_subset_source _) ((B j).faces.face_triangle_subset_source _)
    (by decide) (by decide)
  · rw [funext (B i).faces.right_endpoint_coordinate_map,
      funext (B j).faces.left_endpoint_coordinate_map]
    exact K.adjacent_endpointEdge_image B i j hij
  · rw [(B i).right_endpoint_coordinate_start (S.cut_lt i).le,
      (B j).left_endpoint_coordinate_start (S.cut_lt j).le, hij]

theorem adjacent_bottom_vertices_eq_edge
    (i j : Fin S.count) (hij : i.succ = j.castSucc) :
    (B i).faces.vertex (Fin.last (B i).faces.interface.count, false) =
        (D.edge e.1 e.2).map (S.cut i.succ) ∧
      (B j).faces.vertex (0, false) = (D.edge e.1 e.2).map (S.cut i.succ) := by
  constructor
  · have h := (B i).right_endpoint_coordinate_start (S.cut_lt i).le
    rw [(B i).faces.face_corner_eq_vertex] at h
    change (B i).faces.vertex ((B i).faces.lastCell.succ, false) = _ at h
    have hl : (B i).faces.lastCell.succ = Fin.last (B i).faces.interface.count := by
      apply Fin.ext
      have hn := (B i).faces.interface.count_pos
      simp only [ObliqueBandFaces.lastCell, Fin.val_succ, Fin.val_last]
      omega
    rwa [hl] at h
  · have h := (B j).left_endpoint_coordinate_start (S.cut_lt j).le
    rw [(B j).faces.face_corner_eq_vertex] at h
    change (B j).faces.vertex (0, false) = _ at h
    rwa [hij]

theorem adjacent_bottom_refined_fan
    (hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source)
    (hCinv : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target)
    (g : RiemannianMetric 2 M)
    (lines : ∀ i : Fin S.count, Fin (B i).faces.interface.count × Bool →
      List (EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ))
    (i j : Fin S.count) (hij : i.succ = j.castSucc) :
    (∑ p : Fin (B i).faces.interface.count × Bool,
      meshVertexAngleContribution g ((B i).faces.faceCoordinates p)
        ((TriangleMesh.single ((B i).faces.faceBasis p)
          ((B i).faces.faceBasis p).ind).refineByLines (lines i p))
        ((D.edge e.1 e.2).map (S.cut i.succ))) +
      (∑ p : Fin (B j).faces.interface.count × Bool,
      meshVertexAngleContribution g ((B j).faces.faceCoordinates p)
        ((TriangleMesh.single ((B j).faces.faceBasis p)
          ((B j).faces.faceBasis p).ind).refineByLines (lines j p))
        ((D.edge e.1 e.2).map (S.cut i.succ))) = Real.pi := by
  have hFi := linearGraphCoordinates_contMDiff C (S.piece i).frame hC hCinv
  have hFj := linearGraphCoordinates_contMDiff C (S.piece j).frame hC hCinv
  obtain ⟨hqi, hqj⟩ := K.adjacent_bottom_vertices_eq_edge B i j hij
  have hfan_i := (B i).faces.last_bottom_refined_vertex_fan
    g (hFi.1) (hFi.2) (lines i)
  have hfan_j := (B j).faces.first_bottom_refined_vertex_fan
    g (hFj.1) (hFj.2) (lines j)
  rw [hqi] at hfan_i
  rw [hqj] at hfan_j
  rw [hfan_i, hfan_j]
  obtain ⟨ci, hci, hvi⟩ := (B i).last_bottom_velocity_pos_smul_edge
    (S.cut_lt i) hC
  obtain ⟨cj, hcj, hvj⟩ := (B j).first_bottom_velocity_pos_smul_edge
    (S.cut_lt j) hC
  obtain ⟨c, hc, hup⟩ := K.adjacent_cut_velocity_pos_smul B hC hCinv i j hij
  have hbase := congrArg (fun t : ℝ =>
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (D.edge e.1 e.2).map t 1 : EuclideanSpace ℝ (Fin 2)))
    (congrArg S.cut hij.symm)
  have hvj' := hvj.trans (congrArg (fun v : EuclideanSpace ℝ (Fin 2) => cj • v) hbase)
  dsimp only [TangentSpace] at hvi hvj' hup ⊢
  rw [hup, hvi, hvj', g.cornerAngle_smul_pos_left _ _ _ hci,
    g.cornerAngle_smul_pos_left _ _ _ hcj, g.cornerAngle_smul_pos_right _ _ _ hc,
    g.cornerAngle_neg_left]
  ring

end PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition.OrientedEdgeGraphSubdivision.CutChain
