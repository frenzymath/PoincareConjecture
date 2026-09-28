import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Collars.BandIntersections
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Meshes.ConnectedIntersections

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Topology Manifold ContDiff
open Poincare.Topology.Plane.Curves Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface

private theorem isPreconnected_inter_of_subset_embedded_interval
    {M : Type*} [TopologicalSpace M] [T2Space M] {e : ℝ → M}
    (he : ContinuousOn e (Icc (0 : ℝ) 1)) (hinj : InjOn e (Icc (0 : ℝ) 1))
    {A B : Set M} (hA : IsPreconnected A) (hB : IsPreconnected B)
    (hAsub : A ⊆ e '' Icc (0 : ℝ) 1) (hBsub : B ⊆ e '' Icc (0 : ℝ) 1) :
    IsPreconnected (A ∩ B) := by
  let f : Icc (0 : ℝ) 1 → M := fun t => e t
  have hf : Continuous f := continuousOn_iff_continuous_domRestrict.mp he
  have hfi : Function.Injective f := fun s t h => Subtype.ext (hinj s.2 t.2 h)
  have hA' : A ⊆ range f := by
    rintro q hq
    obtain ⟨t, ht, rfl⟩ := hAsub hq
    exact ⟨⟨t, ht⟩, rfl⟩
  have hB' : B ⊆ range f := by
    rintro q hq
    obtain ⟨t, ht, rfl⟩ := hBsub hq
    exact ⟨⟨t, ht⟩, rfl⟩
  let U : Set ℝ := Subtype.val '' (f ⁻¹' A)
  let V : Set ℝ := Subtype.val '' (f ⁻¹' B)
  have hU : IsPreconnected U :=
    (hA.preimage_of_isClosedMap hfi hf.isClosedMap hA').image Subtype.val
      continuous_subtype_val.continuousOn
  have hV : IsPreconnected V :=
    (hB.preimage_of_isClosedMap hfi hf.isClosedMap hB').image Subtype.val
      continuous_subtype_val.continuousOn
  have hUsub : U ⊆ Icc (0 : ℝ) 1 := by rintro _ ⟨t, _, rfl⟩; exact t.2
  have hVsub : V ⊆ Icc (0 : ℝ) 1 := by rintro _ ⟨t, _, rfl⟩; exact t.2
  have hUA : e '' U = A := by
    dsimp only [U]
    rw [image_image]
    exact image_preimage_eq_of_subset hA'
  have hVB : e '' V = B := by
    dsimp only [V]
    rw [image_image]
    exact image_preimage_eq_of_subset hB'
  rw [← hUA, ← hVB, ← hinj.image_inter hUsub hVsub]
  exact (isPreconnected_iff_ordConnected.mpr
    ((isPreconnected_iff_ordConnected.mp hU).inter
      (isPreconnected_iff_ordConnected.mp hV))).image e
    (he.mono (inter_subset_left.trans hUsub))

namespace SmoothGraphBandPair

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M}
  {lo hi : ℝ → ℝ} {a b : ℝ} {hab : a < b}
  (B : SmoothGraphBandPair F lo hi hab)

omit [T2Space M] in

theorem lower_edge_slice {z : M} (hz : z ∈ F '' coordinateGraphBand lo hi a b)
    (hy : (collarParameterEquiv (F.symm z)).2 = lo (collarParameterEquiv (F.symm z)).1) :
    z ∈ (B.lower.boundary 2).map '' Icc (0 : ℝ) 1 := by
  obtain ⟨q, hq, rfl⟩ := hz
  rw [F.left_inv (B.band_subset_source hq)] at hy
  let t : ℝ := ((collarParameterEquiv q).1 - a) / (b - a)
  have ht : t ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (sub_nonneg.mpr hq.1.1) (sub_pos.mpr hab).le,
      (div_le_one (sub_pos.mpr hab)).mpr (sub_le_sub_right hq.1.2 a)⟩
  have heq : a + t * (b - a) = (collarParameterEquiv q).1 := by
    dsimp [t]
    rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hab.ne')]
    ring
  refine ⟨t, ht, ?_⟩
  rw [B.lower_edge, heq]
  apply congrArg F
  apply collarParameterEquiv.injective
  rw [collarParameterEquiv.apply_symm_apply]
  exact Prod.ext rfl hy.symm

omit [T2Space M] in

theorem upper_bottom_vertex {z : M} (hz : z ∈ B.upper.carrier)
    (hbottom : (collarParameterEquiv (F.symm z)).2 =
      lo (collarParameterEquiv (F.symm z)).1) :
    z = F (collarParameterEquiv.symm (a, lo a)) := by
  rw [B.upper.carrier_eq_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  rw [B.upper_source] at hw
  have hrect : w 0 ∈ Icc a b ∧ w 1 ∈ Icc (0 : ℝ) 1 := by
    change w ∈ {z : EuclideanSpace ℝ (Fin 2) | z 0 ∈ Icc a b ∧ z 1 ∈ Icc (0 : ℝ) 1}
    rw [← rectangle_triangle_union hab zero_lt_one]
    exact Or.inr hw
  have hband : collarParameterEquiv.symm (graphStripMap lo hi (collarParameterEquiv w)) ∈
      coordinateGraphBand lo hi a b := by
    change collarParameterEquiv
      (collarParameterEquiv.symm (graphStripMap lo hi (collarParameterEquiv w))) ∈
        {q : ℝ × ℝ | q.1 ∈ Icc a b ∧ lo q.1 ≤ q.2 ∧ q.2 ≤ hi q.1}
    rw [collarParameterEquiv.apply_symm_apply, ← graphStripMap_image_rectangle B.gap]
    exact ⟨collarParameterEquiv w, hrect, rfl⟩
  rw [B.upper_map, B.lower_map, F.left_inv (B.band_subset_source hband),
    collarParameterEquiv.apply_symm_apply] at hbottom
  change lo (w 0) + w 1 * (hi (w 0) - lo (w 0)) = lo (w 0) at hbottom
  have hy : w 1 = 0 := by nlinarith [B.gap (w 0) hrect.1]
  have hcoord := (mem_rectangleUpperBasis_convexHull hab zero_lt_one w).mp hw
  simp only [sub_zero, div_one, hy] at hcoord
  have hx : w 0 = a := by
    have h := (div_le_iff₀ (sub_pos.mpr hab)).mp hcoord.2.1
    linarith [hrect.1.1]
  rw [B.upper_map, B.lower_map]
  apply congrArg F
  apply congrArg collarParameterEquiv.symm
  change (w 0, lo (w 0) + w 1 * (hi (w 0) - lo (w 0))) = (a, lo a)
  simp [hx, hy]

end SmoothGraphBandPair

namespace FiniteChartRegionDecomposition.OrientedGraphPiece.FixedStripBandFaces

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {D : FiniteChartRegionDecomposition (M := M)} {e : D.EdgeIndex} {R : D.regions}
  {C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M} {a b : ℝ}
  {G : D.OrientedGraphPiece e R C a b} {ua wa ub wb δ ra rb : ℝ}
  {P : TransverseGraphCuts G.lower (G.parameter a) (G.parameter b) ua wa ub wb}
  (B : G.FixedStripBandFaces P δ ra rb)
  (hzero : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z : ℝ, 0 ≤ z → z < δ →
    (G.strip P (t, z) ∈ chartDiskBoundaryUnion D.centers D.radius ↔ z = 0))

include hzero

omit [T2Space M] in
private theorem arrangement_iff_height_zero {q : M} (hq : q ∈ B.faces.carrier) :
    q ∈ chartDiskBoundaryUnion D.centers D.radius ↔
      (collarParameterEquiv (B.faces.coordinates.symm q)).2 = 0 := by
  rw [B.carrier_eq_fixed_strip] at hq
  obtain ⟨z, hz, rfl⟩ := hq
  have hband : collarParameterEquiv.symm z ∈ B.faces.band := by
    rw [B.faces.band_eq_subgraph]
    simpa only [mem_ofPred_eq, collarParameterEquiv.apply_symm_apply] using hz
  have hinv : B.faces.coordinates.symm (G.strip P z) = collarParameterEquiv.symm z := by
    rw [← B.coordinates_eq z]
    exact B.faces.coordinates.left_inv (B.faces.band_subset_source hband)
  rw [hinv, collarParameterEquiv.apply_symm_apply]
  exact hzero z.1 hz.1 z.2 hz.2.1 (hz.2.2.trans_lt (B.height_bounds hz.1).2)

theorem lower_carrier_inter_arrangement (i : Fin B.faces.interface.count) :
    (B.faces.pair i).lower.carrier ∩ chartDiskBoundaryUnion D.centers D.radius =
      ((B.faces.pair i).lower.boundary 2).map '' Icc (0 : ℝ) 1 := by
  apply subset_antisymm
  · rintro q ⟨hq, hK⟩
    exact (B.faces.pair i).lower_edge_slice ((B.faces.pair i).carrier_subset false hq)
      ((B.arrangement_iff_height_zero hzero (subset_iUnion
        (fun j => (B.faces.face j).carrier) (i, false) hq)).mp hK)
  · rintro q ⟨t, ht, rfl⟩
    have hface : ((B.faces.pair i).lower.boundary 2).map t ∈ (B.faces.pair i).lower.carrier :=
      (B.faces.pair i).lower.isClosed_carrier.frontier_subset
        ((B.faces.pair i).lower.boundary_image_subset_frontier 2 ⟨t, ht, rfl⟩)
    refine ⟨hface, (B.arrangement_iff_height_zero hzero (subset_iUnion
      (fun j => (B.faces.face j).carrier) (i, false) hface)).mpr ?_⟩
    rw [(B.faces.pair i).lower_edge]
    have hx : B.faces.cut i.castSucc + t * (B.faces.cut i.succ - B.faces.cut i.castSucc) ∈
        Icc (B.faces.cut i.castSucc) (B.faces.cut i.succ) := by
      constructor <;> nlinarith [B.faces.cut_strictMono (Fin.castSucc_lt_succ (i := i)), ht.1, ht.2]
    have hsource : collarParameterEquiv.symm
        (B.faces.cut i.castSucc + t * (B.faces.cut i.succ - B.faces.cut i.castSucc), 0) ∈
        B.faces.coordinates.source := (B.faces.pair i).band_subset_source
      ⟨hx, le_rfl, ((B.faces.pair i).gap _ hx).le⟩
    rw [B.faces.coordinates.left_inv hsource, collarParameterEquiv.apply_symm_apply]

omit [T2Space M] in

theorem upper_carrier_inter_arrangement_subset_vertex (i : Fin B.faces.interface.count) :
    (B.faces.pair i).upper.carrier ∩ chartDiskBoundaryUnion D.centers D.radius ⊆
      {B.faces.vertex (i.castSucc, false)} := by
  rintro q ⟨hq, hK⟩
  exact (B.faces.pair i).upper_bottom_vertex hq
    ((B.arrangement_iff_height_zero hzero (subset_iUnion
      (fun j => (B.faces.face j).carrier) (i, true) hq)).mp hK)

theorem face_arrangement_trace (i : Fin B.faces.interface.count × Bool) :
    IsPreconnected ((B.faces.face i).carrier ∩ chartDiskBoundaryUnion D.centers D.radius) ∧
      ∃ k : Fin 3, (B.faces.face i).carrier ∩ chartDiskBoundaryUnion D.centers D.radius ⊆
        ((B.faces.face i).boundary k).map '' Icc (0 : ℝ) 1 := by
  rcases i with ⟨i, side⟩
  cases side
  · refine ⟨?_, 2, (B.lower_carrier_inter_arrangement hzero i).subset⟩
    change IsPreconnected ((B.faces.pair i).lower.carrier ∩ _)
    rw [B.lower_carrier_inter_arrangement hzero i]
    exact isPreconnected_Icc.image _ ((B.faces.pair i).lower.boundary 2).smooth.continuousOn
  · have hsub := B.upper_carrier_inter_arrangement_subset_vertex hzero i
    refine ⟨(show ((B.faces.pair i).upper.carrier ∩
        chartDiskBoundaryUnion D.centers D.radius).Subsingleton from
      fun _ hx _ hy => (mem_singleton_iff.mp (hsub hx)).trans
        (mem_singleton_iff.mp (hsub hy)).symm).isPreconnected, 2, ?_⟩
    intro q hq
    have heq := mem_singleton_iff.mp (hsub hq)
    refine ⟨0, by simp, ?_⟩
    change ((B.faces.pair i).upper.boundary 2).map 0 = q
    rw [heq, (B.faces.pair i).left_edge]
    simp [ObliqueBandFaces.vertex]

end FiniteChartRegionDecomposition.OrientedGraphPiece.FixedStripBandFaces

namespace FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  (D : FiniteChartRegionDecomposition (M := M))
  (chart : D.regions → D.centers) (cut : D.EdgeIndex → Bool → ℝ)
  (S : ∀ p : D.IncidentEdgeIndex,
    D.OrientedEdgeGraphSubdivision p.1.2 p.1.1
      (chartAt (EuclideanSpace ℝ (Fin 2)) (chart p.1.1 : M)).symm
      (cut p.1.2 false) (1 - cut p.1.2 true))
  {dLeft dRight : D.IncidentEdgeIndex → EuclideanSpace ℝ (Fin 2)}
  (K : ∀ p, (S p).CutChain (dLeft p) (dRight p)) {δ r : ℝ}
  (B : ∀ p i, ((S p).piece i).FixedStripBandFaces ((K p).graphCuts i) δ r r)

set_option maxHeartbeats 600000 in

theorem cross_region_band_faces_coordinate_intersection
    (hcut : ∀ e t, cut e t ∈ Ioo (0 : ℝ) (1 / 3))
    (hregion : ∀ p i, (B p i).faces.carrier ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ p.1.1))
    (hzero : ∀ p i, ∀ t ∈ Icc (0 : ℝ) 1, ∀ z : ℝ, 0 ≤ z → z < δ →
      (((S p).piece i).strip ((K p).graphCuts i) (t, z) ∈
        chartDiskBoundaryUnion D.centers D.radius ↔ z = 0))
    (i j : D.IncidentGraphPieceIndex chart cut S) (hne : i.1.1.1 ≠ j.1.1.1)
    (v : Fin (B i.1 i.2).faces.interface.count × Bool)
    (w : Fin (B j.1 j.2).faces.interface.count × Bool) :
    CoordinateTriangleBoundaryIntersection
      ((B i.1 i.2).faces.faceCoordinates v) ((B j.1 j.2).faces.faceCoordinates w)
      ((B i.1 i.2).faces.faceBasis v) ((B j.1 j.2).faces.faceBasis w) := by
  have hsub (i : D.IncidentGraphPieceIndex chart cut S)
      (v : Fin (B i.1 i.2).faces.interface.count × Bool) :
      ((B i.1 i.2).faces.face v).carrier ⊆ (B i.1 i.2).faces.carrier :=
    subset_iUnion (fun v => ((B i.1 i.2).faces.face v).carrier) v
  have htrace (i : D.IncidentGraphPieceIndex chart cut S)
      (v : Fin (B i.1 i.2).faces.interface.count × Bool) :
      ((B i.1 i.2).faces.face v).carrier ∩ chartDiskBoundaryUnion D.centers D.radius ⊆
        (S i.1).pieceArc i.2 := by
    have h := (B i.1 i.2).carrier_inter_arrangement ((S i.1).cut_lt i.2) (hzero i.1 i.2)
    exact (inter_subset_inter_left _ (hsub i v)).trans h.subset
  have hinter := D.inter_eq_arrangement_traces hne
    (show ((B i.1 i.2).faces.face v).carrier \ chartDiskBoundaryUnion D.centers D.radius ⊆
      connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ i.1.1.1 from
      fun q hq => D.region_closure_diff_arrangement_subset _
        ⟨hregion i.1 i.2 (hsub i v hq.1), hq.2⟩)
    (show ((B j.1 j.2).faces.face w).carrier \ chartDiskBoundaryUnion D.centers D.radius ⊆
      connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ j.1.1.1 from
      fun q hq => D.region_closure_diff_arrangement_subset _
        ⟨hregion j.1 j.2 (hsub j w hq.1), hq.2⟩)
  by_cases he : i.1.1.2 = j.1.1.2
  · obtain ⟨hvi, k, hk⟩ := (B i.1 i.2).face_arrangement_trace (hzero i.1 i.2) v
    obtain ⟨hwj, l, hl⟩ := (B j.1 j.2).face_arrangement_trace (hzero j.1 j.2) w
    have hconnected : IsPreconnected
        (((B i.1 i.2).faces.face v).carrier ∩ ((B j.1 j.2).faces.face w).carrier) := by
      rw [hinter]
      apply isPreconnected_inter_of_subset_embedded_interval
        (D.edge i.1.1.2.1 i.1.1.2.2).smooth.continuousOn
        (D.edge_injective i.1.1.2.1 i.1.1.2.2) hvi hwj
      · exact (htrace i v).trans (((S i.1).pieceArc_subset_open_edge i.2).trans
          (image_mono Ioo_subset_Icc_self))
      · have h := (htrace j w).trans (((S j.1).pieceArc_subset_open_edge j.2).trans
          (image_mono Ioo_subset_Icc_self))
        have hemap := congrArg (fun e : D.EdgeIndex => (D.edge e.1 e.2).map) he
        rw [hemap]
        exact h
    have hedge (p : D.IncidentGraphPieceIndex chart cut S)
        (v : Fin (B p.1 p.2).faces.interface.count × Bool) (k : Fin 3) :
        (((B p.1 p.2).faces.face v).boundary k).map '' Icc (0 : ℝ) 1 =
          (B p.1 p.2).faces.faceCoordinates v '' affineSegment ℝ
            ((B p.1 p.2).faces.faceBasis v (k.succAbove 0))
            ((B p.1 p.2).faces.faceBasis v (k.succAbove 1)) := by
      rw [(B p.1 p.2).faces.face_boundary_image, image_comp]
      apply congrArg (fun A => (B p.1 p.2).faces.faceCoordinates v '' A)
      unfold affineSegment
      congr 1
      funext t
      simp [affineChartSegment, AffineMap.lineMap_apply, add_comm]
    refine CoordinateTriangleBoundaryIntersection.of_isPreconnected_inter
      _ _ _ _ ((B i.1 i.2).faces.face_triangle_subset_source v)
      ((B j.1 j.2).faces.face_triangle_subset_source w) ?_ k l ?_ ?_
    · simpa only [← (B i.1 i.2).faces.face_carrier_eq_coordinates v,
        ← (B j.1 j.2).faces.face_carrier_eq_coordinates w] using hconnected
    · rw [← (B i.1 i.2).faces.face_carrier_eq_coordinates v,
        ← (B j.1 j.2).faces.face_carrier_eq_coordinates w, ← hedge i v k, hinter]
      exact inter_subset_left.trans hk
    · rw [← (B i.1 i.2).faces.face_carrier_eq_coordinates v,
        ← (B j.1 j.2).faces.face_carrier_eq_coordinates w, ← hedge j w l, hinter]
      exact inter_subset_right.trans hl
  · apply CoordinateTriangleBoundaryIntersection.disjoint
    rw [← (B i.1 i.2).faces.face_carrier_eq_coordinates v,
      ← (B j.1 j.2).faces.face_carrier_eq_coordinates w]
    apply disjoint_iff_inter_eq_empty.mpr
    rw [hinter]
    exact ((D.incident_middleArc_pieceArcs_disjoint_of_edges_ne chart hcut S he i.2 j.2).mono
      (htrace i v) (htrace j w)).inter_eq

end FiniteChartRegionDecomposition
end PoincareConjecture.Topology.Surface
