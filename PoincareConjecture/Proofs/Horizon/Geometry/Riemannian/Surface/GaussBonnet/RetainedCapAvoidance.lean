import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedCollarGerms
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.BottomCuts
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.Arcs









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  (T : RetainedCoordinateTriangulation (M := S))

omit [T2Space S] in
theorem not_mem_cap_on_open_trimmed_arc
    (e : T.decomposition.EdgeIndex) {t : ℝ}
    (ht : t ∈ Ioo (T.cut e false) (1 - T.cut e true))
    (p : T.decomposition.vertices) (s : Bool × Bool) :
    (T.decomposition.edge e.1 e.2).map t ∉ ((T.caps p).face s).carrier := by
  intro hc
  have htunit : t ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [(T.cut_mem e false).1, (T.cut_mem e true).1, ht.1, ht.2]
  have hK : (T.decomposition.edge e.1 e.2).map t ∈
      chartDiskBoundaryUnion T.decomposition.centers T.decomposition.radius := by
    rw [← T.decomposition.boundary_cover]
    exact mem_iUnion.mpr ⟨e, mem_image_of_mem _ (Ioo_subset_Icc_self htunit)⟩
  have hfront : (T.decomposition.edge e.1 e.2).map t ∈ frontier
      (connectedComponentIn
        (chartDiskBoundaryUnion T.decomposition.centers T.decomposition.radius)ᶜ
          (T.region p s : S)) :=
    ⟨T.cap_regions p s hc, fun h => connectedComponentIn_subset _ _ (interior_subset h) hK⟩
  let a : T.decomposition.IncidentEdgeIndex :=
    ⟨(T.region p s, e), (T.decomposition.edge_interior_incidence e t htunit (T.region p s)).mp hfront⟩
  have hcover : (T.decomposition.edge e.1 e.2).map t ∈ ⋃ i, (T.graphs a).pieceArc i := by
    rw [(T.graphs a).iUnion_pieceArc]
    exact mem_image_of_mem _ (Ioo_subset_Icc_self ht)
  obtain ⟨i, hi⟩ := mem_iUnion.mp hcover
  have hb : (T.decomposition.edge e.1 e.2).map t ∈ (T.bands a i).faces.carrier := by
    have h := hi
    change (T.decomposition.edge e.1 e.2).map t ∈
      (T.decomposition.edge a.1.2.1 a.1.2.2).map ''
        Icc ((T.graphs a).cut i.castSucc) ((T.graphs a).cut i.succ) at h
    rw [← T.band_boundary a i] at h
    exact h.1
  have hlower : (T.decomposition.edge e.1 e.2).map t ∈ (T.bands a i).faces.lowerArc := by
    rw [(T.chains a).lowerArc_eq_original (T.bands a) i]
    exact hi
  have hregional : (T.decomposition.edge e.1 e.2).map t ∈
      T.decomposition.vertexCapsInRegion T.caps T.region a.1.1 :=
    mem_iUnion.mpr ⟨⟨(p, s), rfl⟩, hc⟩
  have hmeet := T.band_caps a i ▸
    (show (T.decomposition.edge e.1 e.2).map t ∈
      (T.bands a i).faces.carrier ∩
        T.decomposition.vertexCapsInRegion T.caps T.region a.1.1 from ⟨hb, hregional⟩)
  rcases hmeet with hleft | hright
  · split_ifs at hleft with hfirst
    · subst i
      have hcut : (T.decomposition.edge e.1 e.2).map t ∈
          ((T.bands a (T.graphs a).firstPiece).faces.endpointEdge false).map '' Icc (0 : ℝ) 1 := by
        rw [(T.bands a (T.graphs a).firstPiece).faces.endpointEdge_image]
        change (T.decomposition.edge e.1 e.2).map t ∈
          (T.bands a (T.graphs a).firstPiece).faces.leftCut
        rwa [T.first_band_leftCut_eq_chordSegment a]
      have heq := (T.bands a (T.graphs a).firstPiece).faces.eq_endpoint_of_mem_lowerArc_and_endpointCut
        false hlower hcut
      have hstart := (T.bands a (T.graphs a).firstPiece).left_endpoint_coordinate_start
        ((T.graphs a).cut_lt (T.graphs a).firstPiece).le
      have hcoord := (T.bands a (T.graphs a).firstPiece).faces.left_endpoint_coordinate_map 0
      simp only [AffineMap.lineMap_apply_zero] at hcoord
      rw [← hcoord, hstart, (T.graphs a).firstPiece_castSucc, (T.graphs a).cut_first] at heq
      have hte := T.decomposition.edge_injective e.1 e.2
        (Ioo_subset_Icc_self htunit)
        (show T.cut e false ∈ Icc (0 : ℝ) 1 from
          ⟨(T.cut_mem e false).1.le, by linarith [(T.cut_mem e false).2]⟩) heq
      exact ht.1.ne hte.symm
    · exact hleft
  · split_ifs at hright with hlast
    · subst i
      have hcut : (T.decomposition.edge e.1 e.2).map t ∈
          ((T.bands a (T.graphs a).lastPiece).faces.endpointEdge true).map '' Icc (0 : ℝ) 1 := by
        rw [(T.bands a (T.graphs a).lastPiece).faces.endpointEdge_image]
        change (T.decomposition.edge e.1 e.2).map t ∈
          (T.bands a (T.graphs a).lastPiece).faces.rightCut
        rwa [T.last_band_rightCut_eq_chordSegment a]
      have heq := (T.bands a (T.graphs a).lastPiece).faces.eq_endpoint_of_mem_lowerArc_and_endpointCut
        true hlower hcut
      have hstart := (T.bands a (T.graphs a).lastPiece).right_endpoint_coordinate_start
        ((T.graphs a).cut_lt (T.graphs a).lastPiece).le
      have hcoord := (T.bands a (T.graphs a).lastPiece).faces.right_endpoint_coordinate_map 0
      simp only [AffineMap.lineMap_apply_zero] at hcoord
      rw [← hcoord, hstart, (T.graphs a).lastPiece_succ, (T.graphs a).cut_last] at heq
      have hte := T.decomposition.edge_injective e.1 e.2
        (Ioo_subset_Icc_self htunit)
        (show 1 - T.cut e true ∈ Icc (0 : ℝ) 1 from
          ⟨by linarith [(T.cut_mem e true).2], by linarith [(T.cut_mem e true).1]⟩) heq
      exact ht.2.ne hte
    · exact hright

omit [T2Space S] in
theorem caps_disjoint_open_trimmed_arc
    (p : T.decomposition.vertices) (s : Bool × Bool) (e : T.decomposition.EdgeIndex) :
    Disjoint ((T.caps p).face s).carrier
      ((T.decomposition.edge e.1 e.2).map '' Ioo (T.cut e false) (1 - T.cut e true)) := by
  apply disjoint_left.mpr
  rintro q hq ⟨t, ht, rfl⟩
  exact T.not_mem_cap_on_open_trimmed_arc e ht p s hq

end PoincareConjecture.Topology.Surface.RetainedCoordinateTriangulation
