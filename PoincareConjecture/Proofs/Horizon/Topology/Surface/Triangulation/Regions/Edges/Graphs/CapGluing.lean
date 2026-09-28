import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.CapAttachments
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Vertices.ChordRemainders
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Bands.Gluing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology Manifold ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture.Topology.Surface
namespace FiniteChartRegionDecomposition.OrientedGraphPiece

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {D : FiniteChartRegionDecomposition (M := M)} {e : D.EdgeIndex} {R : D.regions}
  {C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M} {a b : ℝ}
  (G : D.OrientedGraphPiece e R C a b) {ua wa ub wb : ℝ}
  (Q : TransverseGraphCuts G.lower (G.parameter a) (G.parameter b) ua wa ub wb)

omit [T2Space M] in
theorem strip_left_parameter (hab : a ≤ b) {u : ℝ} (hu : u ∈ Q.left.parameter.source) :
    G.strip Q (0, Q.left.parameter u) =
      C (C.symm ((D.edge e.1 e.2).map a) + u • G.frame.symm (ua, wa)) := by
  have hbase : G.frame.symm (G.parameter a, G.lower (G.parameter a)) =
      C.symm ((D.edge e.1 e.2).map a) := by
    have h := congrArg G.frame.symm (G.graph_coordinates a
      (G.interval_source (left_mem_Icc.mpr hab)))
    simpa only [G.frame.symm_apply_apply] using h.symm
  rw [G.strip_apply]
  simp only [zero_mul, add_zero]
  change C (G.frame.symm (Q.left.horizontal (Q.left.parameter u),
    G.lower (Q.left.horizontal (Q.left.parameter u)) + Q.left.parameter u)) = _
  rw [Q.left.horizontal_parameter hu, Q.left.map_eq]
  have hpair : (G.parameter a + u * ua,
      G.lower (G.parameter a + u * ua) +
        transverseCutHeight G.lower (G.parameter a) ua wa u) =
      (G.parameter a, G.lower (G.parameter a)) + u • (ua, wa) := by
    ext <;> simp [transverseCutHeight, smul_eq_mul]
  rw [hpair, map_add, map_smul, hbase]

omit [T2Space M] in
theorem strip_right_parameter (hab : a ≤ b) {u : ℝ} (hu : u ∈ Q.right.parameter.source) :
    G.strip Q (1, Q.right.parameter u) =
      C (C.symm ((D.edge e.1 e.2).map b) + u • G.frame.symm (ub, wb)) := by
  have hbase : G.frame.symm (G.parameter b, G.lower (G.parameter b)) =
      C.symm ((D.edge e.1 e.2).map b) := by
    have h := congrArg G.frame.symm (G.graph_coordinates b
      (G.interval_source (right_mem_Icc.mpr hab)))
    simpa only [G.frame.symm_apply_apply] using h.symm
  rw [G.strip_apply]
  have hx (z : ℝ) : Q.A z + (Q.B z - Q.A z) = Q.B z := by ring
  simp only [one_mul, hx]
  change C (G.frame.symm (Q.right.horizontal (Q.right.parameter u),
    G.lower (Q.right.horizontal (Q.right.parameter u)) + Q.right.parameter u)) = _
  rw [Q.right.horizontal_parameter hu, Q.right.map_eq]
  have hpair : (G.parameter b + u * ub,
      G.lower (G.parameter b + u * ub) +
        transverseCutHeight G.lower (G.parameter b) ub wb u) =
      (G.parameter b, G.lower (G.parameter b)) + u • (ub, wb) := by
    ext <;> simp [transverseCutHeight, smul_eq_mul]
  rw [hpair, map_add, map_smul, hbase]

namespace FixedStripBandFaces

variable {G Q} {δ ra rb : ℝ} (F : G.FixedStripBandFaces Q δ ra rb)

omit [T2Space M] in
theorem open_left_ray_subset_endpointEdge (hab : a ≤ b) :
    (fun u : ℝ => C (C.symm ((D.edge e.1 e.2).map a) +
      u • G.frame.symm (ua, wa))) '' Ioo 0 ra ⊆
        (F.faces.endpointEdge false).map '' Ioo (0 : ℝ) 1 := by
  rintro q ⟨u, hu, rfl⟩
  have hus := Q.left.parameter_Icc_subset_source F.left_parameter_mem (Ioo_subset_Icc_self hu)
  have hz0 : 0 < Q.left.parameter u := by
    simpa only [Q.left.parameter_zero] using Q.left.strictMono Q.left.zero_mem_source hus hu.1
  have hzr : Q.left.parameter u < F.faces.height 0 := by
    rw [F.height_zero]
    exact Q.left.strictMono hus F.left_parameter_mem hu.2
  have hh := F.faces.height_pos (by norm_num : (0 : ℝ) ∈ Icc 0 1)
  refine ⟨Q.left.parameter u / F.faces.height 0,
    ⟨div_pos hz0 hh, (div_lt_one hh).mpr hzr⟩, ?_⟩
  rw [F.faces.endpointEdge_map]
  change F.faces.coordinates (collarParameterEquiv.symm
    (0, Q.left.parameter u / F.faces.height 0 * F.faces.height 0)) = _
  rw [div_mul_cancel₀ _ hh.ne', F.coordinates_eq]
  exact G.strip_left_parameter Q hab hus

omit [T2Space M] in
theorem open_right_ray_subset_endpointEdge (hab : a ≤ b) :
    (fun u : ℝ => C (C.symm ((D.edge e.1 e.2).map b) +
      u • G.frame.symm (ub, wb))) '' Ioo 0 rb ⊆
        (F.faces.endpointEdge true).map '' Ioo (0 : ℝ) 1 := by
  rintro q ⟨u, hu, rfl⟩
  have hus := Q.right.parameter_Icc_subset_source F.right_parameter_mem (Ioo_subset_Icc_self hu)
  have hz0 : 0 < Q.right.parameter u := by
    simpa only [Q.right.parameter_zero] using Q.right.strictMono Q.right.zero_mem_source hus hu.1
  have hzr : Q.right.parameter u < F.faces.height 1 := by
    rw [F.height_one]
    exact Q.right.strictMono hus F.right_parameter_mem hu.2
  have hh := F.faces.height_pos (by norm_num : (1 : ℝ) ∈ Icc 0 1)
  refine ⟨Q.right.parameter u / F.faces.height 1,
    ⟨div_pos hz0 hh, (div_lt_one hh).mpr hzr⟩, ?_⟩
  rw [F.faces.endpointEdge_map]
  change F.faces.coordinates (collarParameterEquiv.symm
    (1, Q.right.parameter u / F.faces.height 1 * F.faces.height 1)) = _
  rw [div_mul_cancel₀ _ hh.ne', F.coordinates_eq]
  exact G.strip_right_parameter Q hab hus

omit [T2Space M] in
theorem left_top_mem_polygonalTop (hab : a ≤ b) :
    C (C.symm ((D.edge e.1 e.2).map a) + ra • G.frame.symm (ua, wa)) ∈
      F.faces.polygonalTop := by
  rw [← F.faces.height_graph_image]
  refine ⟨0, by norm_num, ?_⟩
  change F.faces.coordinates (collarParameterEquiv.symm (0, F.faces.height 0)) = _
  rw [F.coordinates_eq, F.height_zero]
  exact G.strip_left_parameter Q hab F.left_parameter_mem

omit [T2Space M] in
theorem right_top_mem_polygonalTop (hab : a ≤ b) :
    C (C.symm ((D.edge e.1 e.2).map b) + rb • G.frame.symm (ub, wb)) ∈
      F.faces.polygonalTop := by
  rw [← F.faces.height_graph_image]
  refine ⟨1, by norm_num, ?_⟩
  change F.faces.coordinates (collarParameterEquiv.symm (1, F.faces.height 1)) = _
  rw [F.coordinates_eq, F.height_one]
  exact G.strip_right_parameter Q hab F.right_parameter_mem

end FixedStripBandFaces
end FiniteChartRegionDecomposition.OrientedGraphPiece

namespace ChartCircleArrangementVertexPatch.VertexCapFaces

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {radius : M → ℝ} {p : M} {P : ChartCircleArrangementVertexPatch radius p}
  {x : Bool × Bool → M} (B : VertexCapFaces P x)
  {F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M}
  {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
  (band : ObliqueBandFaces F lo a b ua wa ub wb ra rb)

theorem mem_interior_union_band (i : Bool × Bool) (right : Bool)
    {t u : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1)
    (hpoint : ((B.face i).boundary 0).map t = (band.endpointEdge right).map u)
    (hshared : (band.endpointEdge right).map '' Icc (0 : ℝ) 1 ⊆
      ((B.face i).boundary 0).map '' Icc (0 : ℝ) 1)
    (hdisjoint : Disjoint (interior (B.face i).carrier) (interior band.carrier)) :
    ((B.face i).boundary 0).map t ∈ interior ((B.face i).carrier ∪ band.carrier) := by
  let other := ⋃ j : {j : Fin 3 // j ≠ 0}, ((B.face i).boundary j).map '' Icc (0 : ℝ) 1
  have hother : IsCompact other := isCompact_iUnion (fun j =>
    isCompact_Icc.image_of_continuousOn ((B.face i).boundary j).smooth.continuousOn)
  have hnot : ((B.face i).boundary 0).map t ∉ other := by
    intro h
    obtain ⟨j, hj⟩ := mem_iUnion.mp h
    exact coordinate_triangle_boundary_avoids_other_edges (B.face i) (B.coordinates i)
      (Poincare.Topology.Plane.Triangles.rightTriangleBasis B.scale_pos)
      (B.triangle_subset_source i) (B.boundary_map i) (Ne.symm j.property) ht hj
  obtain ⟨N, hN, huN, hfrontN⟩ := band.exists_endpoint_frontier_neighborhood right hu
  have hregular : closure (interior (B.face i).carrier) = (B.face i).carrier := by
    rw [B.carrier_eq]
    exact coordinate_triangle_closure_interior (B.coordinates i)
      (Poincare.Topology.Plane.Triangles.rightTriangleBasis B.scale_pos) (B.triangle_subset_source i)
  have hchart : ((B.face i).boundary 0).map '' Icc (0 : ℝ) 1 ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) (B.face i).chart).source :=
    ((B.face i).boundary_image_subset_frontier 0).trans
      ((B.face i).isClosed_carrier.frontier_subset.trans (B.face i).carrier_subset_chart)
  apply ((B.face i).boundary 0).mem_interior_union_of_local_frontiers (B.face i).chart
    (B.boundary_injective i 0) hchart ((B.face i).interior_boundary_image 0)
    (B.face i).isClosed_carrier band.isClosed_carrier hregular band.closure_interior_carrier
    hdisjoint ht
    ((B.face i).isClosed_carrier.frontier_subset
      ((B.face i).boundary_image_subset_frontier 0 ⟨t, Ioo_subset_Icc_self ht, rfl⟩))
    (hpoint ▸ band.isClosed_carrier.frontier_subset
      (band.endpointEdge_subset_frontier right ⟨u, Ioo_subset_Icc_self hu, rfl⟩))
    ((hother.isClosed.isOpen_compl.inter hN).mem_nhds ⟨hnot, hpoint ▸ huN⟩)
  · rintro q ⟨hqN, hqfront⟩
    rw [(B.face i).boundary_carrier] at hqfront
    obtain ⟨j, hj⟩ := mem_iUnion.mp hqfront
    by_cases hj0 : j = 0
    · simpa only [hj0] using hj
    · exact False.elim (hqN.1 (mem_iUnion.mpr ⟨⟨j, hj0⟩, hj⟩))
  · exact fun q hq => hshared (hfrontN ⟨hq.1.2, hq.2⟩)

end ChartCircleArrangementVertexPatch.VertexCapFaces

namespace FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {D : FiniteChartRegionDecomposition (M := M)}
  {P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M)}
  {region : D.vertices → Bool × Bool → D.regions} {chart : D.regions → M}
  {B : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p)
    (fun s => chart (region p s))}
  {e : D.EdgeIndex} {R : D.regions}

namespace CapGraphEndpoint

variable {a b : ℝ}
  {G : D.OrientedGraphPiece e R (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).symm a b}
  {terminal : Bool} {trim : ℝ} (E : D.CapGraphEndpoint P region chart B e R G terminal trim)

def openChordSegment (r : ℝ) : Set M :=
  (fun u : ℝ => (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).symm
    (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R) (D.edgeFromEndpoint e terminal trim) +
      u • E.direction)) '' Ioo 0 r

omit [T2Space M] in
theorem chordSegment_subset_chord {r : ℝ} (hr : r ≤ 1) :
    E.chordSegment r ⊆
      (((B (D.edgeEndpoint e terminal)).face E.sector).boundary 0).map '' Icc (0 : ℝ) 1 := by
  rintro q ⟨u, hu, rfl⟩
  refine ⟨if E.radialEdge = 1 then 1 - u else u, ?_, (E.chord_map u).symm⟩
  split_ifs <;> constructor <;> linarith [hu.1, hu.2]

omit [T2Space M] in
theorem openChordSegment_subset_open_chord {r : ℝ} (hr : r ≤ 1) :
    E.openChordSegment r ⊆
      (((B (D.edgeEndpoint e terminal)).face E.sector).boundary 0).map '' Ioo (0 : ℝ) 1 := by
  rintro q ⟨u, hu, rfl⟩
  refine ⟨if E.radialEdge = 1 then 1 - u else u, ?_, (E.chord_map u).symm⟩
  split_ifs <;> constructor <;> linarith [hu.1, hu.2]

theorem openChordSegment_eq_openChordAttachment (K : Set M) (r : ℝ)
    (hK : D.edgeFromEndpoint e terminal trim ∈ K) :
    E.openChordSegment r = (B (D.edgeEndpoint e terminal)).openChordAttachment K E.sector
      (decide (E.radialEdge = 1)) r := by
  have hk : (if decide (E.radialEdge = 1) then 1 else 2 : Fin 3) = E.radialEdge := by
    rcases E.radialEdge_valid with h | h <;> simp [h]
  have htip : (((B (D.edgeEndpoint e terminal)).face E.sector).boundary 0).map
      (if decide (E.radialEdge = 1) then 1 else 0) = D.edgeFromEndpoint e terminal trim := by
    rw [(B (D.edgeEndpoint e terminal)).chord_endpoint_eq_radial_tip, hk]
    exact E.radial_end
  rw [(B (D.edgeEndpoint e terminal)).openChordAttachment_eq_ray K E.sector
    (decide (E.radialEdge = 1)) r (htip.symm ▸ hK)]
  simp only [openChordSegment, E.sector_region, ← E.direction_eq, E.chord_base]

end CapGraphEndpoint

namespace OrientedGraphPiece.FixedStripBandFaces

variable {a b ua wa ub wb δ ra rb : ℝ}
  {G : D.OrientedGraphPiece e R (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).symm a b}
  {Q : TransverseGraphCuts G.lower (G.parameter a) (G.parameter b) ua wa ub wb}
  (F : G.FixedStripBandFaces Q δ ra rb)

omit [T2Space M] in

theorem disjoint_cap_interiors (p : D.vertices) (s : Bool × Bool)
    (hs : region p s = R)
    (havoid : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ z : ℝ, |z| < δ →
      Q.coordinates G.parameter.open_target G.lower_smooth (t, z) ∉
        D.graphCapObstacle region chart B R G.frame) :
    Disjoint (interior ((B p).face s).carrier) (interior F.faces.carrier) := by
  apply disjoint_left.mpr
  intro q hcap hband
  have hregional : q ∈ D.vertexCapsInRegion B region R :=
    mem_iUnion.mpr ⟨⟨(p, s), hs⟩, interior_subset hcap⟩
  have hcuts := F.inter_region_caps_subset_cuts havoid ⟨interior_subset hband, hregional⟩
  apply disjoint_left.mp disjoint_interior_frontier hband
  rcases hcuts with hleft | hright
  · exact F.faces.outer_boundaries_subset_frontier (Or.inl (Or.inr hleft))
  · exact F.faces.outer_boundaries_subset_frontier (Or.inr hright)

end OrientedGraphPiece.FixedStripBandFaces

namespace OrientedEdgeGraphSubdivision

variable {cut : D.EdgeIndex → Bool → ℝ}
  {S : D.OrientedEdgeGraphSubdivision e R
    (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).symm (cut e false) (1 - cut e true)}
  (L : D.CapGraphEndpoint P region chart B e R (S.piece S.firstPiece) false (cut e false))
  (T : D.CapGraphEndpoint P region chart B e R (S.piece S.lastPiece) true (cut e true))
  (K : S.CutChain L.direction T.direction)

theorem CutChain.left_attachment_subset_interior {r δ : ℝ} (hr : r ≤ 1)
    (F : (S.piece S.firstPiece).FixedStripBandFaces (K.graphCuts S.firstPiece) δ r r)
    (havoid : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ z : ℝ, |z| < δ →
      (K.graphCuts S.firstPiece).coordinates (S.piece S.firstPiece).parameter.open_target
        (S.piece S.firstPiece).lower_smooth (t, z) ∉
          D.graphCapObstacle region chart B R (S.piece S.firstPiece).frame) :
    L.openChordSegment r ⊆
      interior (((B (D.edgeEndpoint e false)).face L.sector).carrier ∪ F.faces.carrier) := by
  have hcut : F.faces.leftCut = L.chordSegment r := by
    simpa only [Prod.eta, ContinuousLinearEquiv.symm_apply_apply,
      OpenPartialHomeomorph.symm_symm, S.firstPiece_castSucc, S.cut_first, K.first,
      CapGraphEndpoint.chordSegment, edgeFromEndpoint, Bool.false_eq_true, ite_false] using
      F.leftCut_eq_ray (S.cut_lt S.firstPiece).le
  have hopen : L.openChordSegment r ⊆ (F.faces.endpointEdge false).map '' Ioo (0 : ℝ) 1 := by
    simpa only [Prod.eta, ContinuousLinearEquiv.symm_apply_apply,
      OpenPartialHomeomorph.symm_symm, S.firstPiece_castSucc, S.cut_first, K.first,
      CapGraphEndpoint.openChordSegment, edgeFromEndpoint, Bool.false_eq_true, ite_false] using
      F.open_left_ray_subset_endpointEdge (S.cut_lt S.firstPiece).le
  intro q hq
  obtain ⟨t, ht, htq⟩ := L.openChordSegment_subset_open_chord hr hq
  obtain ⟨u, hu, huq⟩ := hopen hq
  rw [← htq]
  apply (B (D.edgeEndpoint e false)).mem_interior_union_band F.faces L.sector false
    ht hu (htq.trans huq.symm) ?_
      (F.disjoint_cap_interiors _ _ L.sector_region havoid)
  rw [F.faces.endpointEdge_image]
  simpa only [Bool.false_eq_true, ite_false, hcut] using L.chordSegment_subset_chord hr

theorem CutChain.right_attachment_subset_interior {r δ : ℝ} (hr : r ≤ 1)
    (F : (S.piece S.lastPiece).FixedStripBandFaces (K.graphCuts S.lastPiece) δ r r)
    (havoid : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ z : ℝ, |z| < δ →
      (K.graphCuts S.lastPiece).coordinates (S.piece S.lastPiece).parameter.open_target
        (S.piece S.lastPiece).lower_smooth (t, z) ∉
          D.graphCapObstacle region chart B R (S.piece S.lastPiece).frame) :
    T.openChordSegment r ⊆
      interior (((B (D.edgeEndpoint e true)).face T.sector).carrier ∪ F.faces.carrier) := by
  have hcut : F.faces.rightCut = T.chordSegment r := by
    simpa only [Prod.eta, ContinuousLinearEquiv.symm_apply_apply,
      OpenPartialHomeomorph.symm_symm, S.lastPiece_succ, S.cut_last, K.last,
      CapGraphEndpoint.chordSegment, edgeFromEndpoint, ite_true] using
      F.rightCut_eq_ray (S.cut_lt S.lastPiece).le
  have hopen : T.openChordSegment r ⊆ (F.faces.endpointEdge true).map '' Ioo (0 : ℝ) 1 := by
    simpa only [Prod.eta, ContinuousLinearEquiv.symm_apply_apply,
      OpenPartialHomeomorph.symm_symm, S.lastPiece_succ, S.cut_last, K.last,
      CapGraphEndpoint.openChordSegment, edgeFromEndpoint, ite_true] using
      F.open_right_ray_subset_endpointEdge (S.cut_lt S.lastPiece).le
  intro q hq
  obtain ⟨t, ht, htq⟩ := T.openChordSegment_subset_open_chord hr hq
  obtain ⟨u, hu, huq⟩ := hopen hq
  rw [← htq]
  apply (B (D.edgeEndpoint e true)).mem_interior_union_band F.faces T.sector true
    ht hu (htq.trans huq.symm) ?_
      (F.disjoint_cap_interiors _ _ T.sector_region havoid)
  rw [F.faces.endpointEdge_image]
  simpa only [ite_true, hcut] using T.chordSegment_subset_chord hr

end OrientedEdgeGraphSubdivision
end FiniteChartRegionDecomposition
end PoincareConjecture.Topology.Surface
