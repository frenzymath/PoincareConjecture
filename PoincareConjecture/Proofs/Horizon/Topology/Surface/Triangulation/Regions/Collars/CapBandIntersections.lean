import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Collars.BandIntersections
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Vertices.ChordRemainders
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Corners.Coordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Topology Manifold ContDiff Classical
open Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

private theorem cap_band_coordinate_intersection_of_cut
    {radius : M → ℝ} {p : M} {P : ChartCircleArrangementVertexPatch radius p}
    {x : Bool × Bool → M} (caps : ChartCircleArrangementVertexPatch.VertexCapFaces P x)
    (s : Bool × Bool)
    {F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M}
    {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
    (B : ObliqueBandFaces F lo a b ua wa ub wb ra rb)
    (cut : Set M) (j₀ : Fin B.interface.count × Bool) (k : Fin 3) (v : M)
    (hinter : (caps.face s).carrier ∩ B.carrier = cut)
    (hcut : cut = ((B.face j₀).boundary k).map '' Icc (0 : ℝ) 1)
    (hcutfront : cut ⊆ frontier B.carrier)
    (hother : ∀ j, j ≠ j₀ → (B.face j).carrier ∩ cut ⊆ {v})
    {c d : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) (hd : d ∈ Icc (0 : ℝ) 1)
    (hchord : cut = ((caps.face s).boundary 0).map '' uIcc c d)
    (j : Fin B.interface.count × Bool) :
    CoordinateTriangleBoundaryIntersection (caps.coordinates s) (B.faceCoordinates j)
      (rightTriangleBasis caps.scale_pos) (B.faceBasis j) := by
  have hsub : (caps.face s).carrier ∩ (B.face j).carrier ⊆ cut := by
    rw [← hinter]
    exact inter_subset_inter_right _ (subset_iUnion (fun v => (B.face v).carrier) j)
  have hfront {q : M} (hq : q ∈ (caps.face s).carrier ∩ (B.face j).carrier) :
      q ∈ frontier (caps.face s).carrier ∧ q ∈ frontier (B.face j).carrier := by
    have hqcut := hsub hq
    have hqband := hcutfront hqcut
    have hqcap : q ∈ frontier (caps.face s).carrier := by
      apply (caps.face s).boundary_image_subset_frontier 0
      rw [hchord] at hqcut
      exact image_mono (uIcc_subset_Icc hc hd) hqcut
    exact ⟨hqcap, ⟨subset_closure hq.2, fun h => hqband.2
      (interior_mono (subset_iUnion _ j) h)⟩⟩
  by_cases hj : j = j₀
  · subst j
    have heq : (caps.face s).carrier ∩ (B.face j₀).carrier = cut := by
      apply subset_antisymm hsub
      intro q hq
      have hqcap := (hinter.symm ▸ hq).1
      exact ⟨hqcap, (B.face j₀).isClosed_carrier.frontier_subset
        ((B.face j₀).boundary_image_subset_frontier k (hcut ▸ hq))⟩
    apply CoordinateTriangleBoundaryIntersection.subsegment 0 k c d 0 1 hc hd (by simp) (by simp)
    · rw [← caps.carrier_eq, ← B.face_carrier_eq_coordinates, heq, hchord, caps.boundary_map]
    · rw [← caps.carrier_eq, ← B.face_carrier_eq_coordinates, heq,
        uIcc_of_le zero_le_one, ← B.face_boundary_image, ← hcut]
  · have hpoint : (caps.face s).carrier ∩ (B.face j).carrier ⊆ {v} :=
      fun _ hq => hother j hj ⟨hq.2, hsub hq⟩
    by_cases hn : ((caps.face s).carrier ∩ (B.face j).carrier).Nonempty
    · obtain ⟨q, hq⟩ := hn
      apply CoordinateTriangleBoundaryIntersection.point q
      · rw [← caps.face_frontier_eq_coordinates]
        exact (hfront hq).1
      · rw [← B.face_frontier_eq_coordinates]
        exact (hfront hq).2
      · rw [← caps.carrier_eq, ← B.face_carrier_eq_coordinates]
        intro z hz
        exact (mem_singleton_iff.mp (hpoint hz)).trans (mem_singleton_iff.mp (hpoint hq)).symm
    · apply CoordinateTriangleBoundaryIntersection.disjoint
      rw [← caps.carrier_eq, ← B.face_carrier_eq_coordinates]
      exact disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hn)

namespace FiniteChartRegionDecomposition

variable {D : FiniteChartRegionDecomposition (M := M)}

namespace CapGraphEndpoint

variable
  {P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M)}
  {region : D.vertices → Bool × Bool → D.regions} {chart : D.regions → M}
  {caps : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p)
    (fun s => chart (region p s))}
  {e : D.EdgeIndex} {R : D.regions} {a b trim : ℝ} {terminal : Bool}
  {g : D.OrientedGraphPiece e R (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).symm a b}
  (E : D.CapGraphEndpoint P region chart caps e R g terminal trim)

theorem tip_mem_cap : D.edgeFromEndpoint e terminal trim ∈
    ((caps (D.edgeEndpoint e terminal)).face E.sector).carrier := by
  rw [← E.radial_end]
  exact ((caps (D.edgeEndpoint e terminal)).face E.sector).isClosed_carrier.frontier_subset
    (((caps (D.edgeEndpoint e terminal)).face E.sector).boundary_image_subset_frontier
      E.radialEdge ⟨1, by simp, rfl⟩)

theorem tip_cap_unique
    (hdisjoint : ∀ p q, p ≠ q → Disjoint (P p).carrier (P q).carrier)
    (hsector : ∀ p i, (P p).sector i ⊆ connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i))
    (hclosed : ∀ p i, (P p).closedSector i ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i)))
    (htrim : trim ∈ Ioo (0 : ℝ) 1)
    (hmatch : ∃ i j : Bool × Bool, ∃ k : Fin 3, i ≠ j ∧ (k = 1 ∨ k = 2) ∧
      ∀ s, s = i ∨ s = j →
        (((caps (D.edgeEndpoint e terminal)).face s).boundary k).map 1 =
          D.edgeFromEndpoint e terminal trim) :
    ∀ p s, region p s = R → D.edgeFromEndpoint e terminal trim ∈ ((caps p).face s).carrier →
      p = D.edgeEndpoint e terminal ∧ s = E.sector := by
  obtain ⟨i, j, k, hij, hk, hend⟩ := hmatch
  obtain ⟨hne, _, hinc⟩ := D.matched_caps_global_incidence P caps region hdisjoint
    hsector hclosed (D.edgeEndpoint e terminal) e terminal htrim hij k hk hend
  have hE := ((hinc _ E.sector).mp E.tip_mem_cap).2
  intro p s hsR hs
  obtain ⟨rfl, hsij⟩ := (hinc p s).mp hs
  refine ⟨rfl, ?_⟩
  rcases hsij with rfl | rfl <;> rcases hE with hE | hE
  · exact hE.symm
  · exfalso
    apply hne
    rw [hsR, ← E.sector_region, hE]
  · exfalso
    apply hne
    rw [← hE, E.sector_region, hsR]
  · exact hE.symm

omit [T2Space M] in

theorem chordSegment_eq_subsegment {r : ℝ} (hr : 0 ≤ r) :
    E.chordSegment r =
      (((caps (D.edgeEndpoint e terminal)).face E.sector).boundary 0).map ''
        uIcc (if E.radialEdge = 1 then 1 else 0)
          (if E.radialEdge = 1 then 1 - r else r) := by
  by_cases he : E.radialEdge = 1
  · simp only [if_pos he, uIcc_of_ge (show 1 - r ≤ 1 by linarith)]
    ext q
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨1 - u, ⟨by linarith [hu.2], by linarith [hu.1]⟩, ?_⟩
      simpa only [if_pos he] using (E.chord_map u).symm
    · rintro ⟨t, ht, rfl⟩
      refine ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
      simpa only [if_pos he, sub_sub_cancel] using E.chord_map (1 - t)
  · simp only [if_neg he, uIcc_of_le hr]
    exact image_congr (fun u _ => by simpa only [if_neg he] using E.chord_map u)

omit [T2Space M] in

theorem positive_chord_mem_sector {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).symm
      (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R) (D.edgeFromEndpoint e terminal trim) +
        u • E.direction) ∈ (P (D.edgeEndpoint e terminal)).sector E.sector := by
  rw [E.chord_map]
  apply (caps (D.edgeEndpoint e terminal)).chord_interior_mem_sector
  split_ifs <;> constructor <;> linarith [hu.1, hu.2]

theorem chordSegment_inter_cap {r : ℝ} (hr : r < 1)
    (hdisjoint : ∀ p q, p ≠ q → Disjoint (P p).carrier (P q).carrier)
    (hunique : ∀ p s, region p s = R →
      D.edgeFromEndpoint e terminal trim ∈ ((caps p).face s).carrier →
        p = D.edgeEndpoint e terminal ∧ s = E.sector)
    (p : D.vertices) (s : Bool × Bool) (hsR : region p s = R) :
    E.chordSegment r ∩ ((caps p).face s).carrier =
      if p = D.edgeEndpoint e terminal ∧ s = E.sector then E.chordSegment r else ∅ := by
  classical
  by_cases hselected : p = D.edgeEndpoint e terminal ∧ s = E.sector
  · rcases hselected with ⟨rfl, rfl⟩
    rw [if_pos ⟨rfl, rfl⟩]
    exact inter_eq_left.mpr (E.chordSegment_subset_cap hr.le)
  · rw [if_neg hselected]
    apply eq_empty_iff_forall_notMem.mpr
    rintro q ⟨⟨u, hu, rfl⟩, hq⟩
    have hp : p = D.edgeEndpoint e terminal := by
      by_contra hp
      exact disjoint_left.mp (hdisjoint p (D.edgeEndpoint e terminal) hp)
        ((caps p).carrier_subset_patch s hq)
        ((caps (D.edgeEndpoint e terminal)).carrier_subset_patch E.sector
          (E.chordSegment_subset_cap hr.le ⟨u, hu, rfl⟩))
    subst p
    have hs : s ≠ E.sector := fun hs => hselected ⟨rfl, hs⟩
    by_cases hu0 : u = 0
    · subst u
      have hchart := (caps (D.edgeEndpoint e terminal)).carrier_subset_chart E.sector E.tip_mem_cap
      rw [E.sector_region] at hchart
      simp only [zero_smul, add_zero,
        (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).left_inv hchart] at hq
      exact hselected (hunique _ s hsR hq)
    · exact disjoint_left.mp ((P (D.edgeEndpoint e terminal)).sector_disjoint_closedSector hs.symm)
        (E.positive_chord_mem_sector ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0), hu.2.trans_lt hr⟩)
        ((caps (D.edgeEndpoint e terminal)).carrier_subset_sector s hq)

end CapGraphEndpoint

namespace OrientedEdgeGraphSubdivision.CutChain

variable
  {P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M)}
  {region : D.vertices → Bool × Bool → D.regions} {chart : D.regions → M}
  {caps : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p)
    (fun s => chart (region p s))}
  {cut : D.EdgeIndex → Bool → ℝ} {e : D.EdgeIndex} {R : D.regions}
  {S : D.OrientedEdgeGraphSubdivision e R
    (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).symm (cut e false) (1 - cut e true)}
  (L : D.CapGraphEndpoint P region chart caps e R (S.piece S.firstPiece) false (cut e false))
  (T : D.CapGraphEndpoint P region chart caps e R (S.piece S.lastPiece) true (cut e true))
  (K : S.CutChain L.direction T.direction)
  {r δ : ℝ} (i : Fin S.count) (B : (S.piece i).FixedStripBandFaces (K.graphCuts i) δ r r)

omit [T2Space M] in
theorem first_leftCut_eq_chordSegment (hi : i = S.firstPiece) :
    B.faces.leftCut = L.chordSegment r := by
  subst i
  simpa only [Prod.eta, ContinuousLinearEquiv.symm_apply_apply,
    OpenPartialHomeomorph.symm_symm, S.firstPiece_castSucc, S.cut_first, K.first,
    CapGraphEndpoint.chordSegment, edgeFromEndpoint, Bool.false_eq_true, ite_false] using
    B.leftCut_eq_ray (S.cut_lt S.firstPiece).le

omit [T2Space M] in
theorem last_rightCut_eq_chordSegment (hi : i = S.lastPiece) :
    B.faces.rightCut = T.chordSegment r := by
  subst i
  simpa only [Prod.eta, ContinuousLinearEquiv.symm_apply_apply,
    OpenPartialHomeomorph.symm_symm, S.lastPiece_succ, S.cut_last, K.last,
    CapGraphEndpoint.chordSegment, edgeFromEndpoint, ite_true] using
    B.rightCut_eq_ray (S.cut_lt S.lastPiece).le

theorem band_inter_cap
    (hr : r < 1)
    (hdisjoint : ∀ p q, p ≠ q → Disjoint (P p).carrier (P q).carrier)
    (huniqueL : ∀ p s, region p s = R →
      D.edgeFromEndpoint e false (cut e false) ∈ ((caps p).face s).carrier →
        p = D.edgeEndpoint e false ∧ s = L.sector)
    (huniqueT : ∀ p s, region p s = R →
      D.edgeFromEndpoint e true (cut e true) ∈ ((caps p).face s).carrier →
        p = D.edgeEndpoint e true ∧ s = T.sector)
    (hbandCaps : B.faces.carrier ∩ D.vertexCapsInRegion caps region R =
      (if i = S.firstPiece then L.chordSegment r else ∅) ∪
        (if i = S.lastPiece then T.chordSegment r else ∅))
    (p : D.vertices) (s : Bool × Bool) (hsR : region p s = R) :
    B.faces.carrier ∩ ((caps p).face s).carrier =
      (if i = S.firstPiece ∧ p = D.edgeEndpoint e false ∧ s = L.sector
        then L.chordSegment r else ∅) ∪
      (if i = S.lastPiece ∧ p = D.edgeEndpoint e true ∧ s = T.sector
        then T.chordSegment r else ∅) := by
  have hcap : ((caps p).face s).carrier ⊆ D.vertexCapsInRegion caps region R := by
    intro q hq
    exact mem_iUnion.mpr ⟨⟨(p, s), hsR⟩, hq⟩
  have heq : B.faces.carrier ∩ ((caps p).face s).carrier =
      (B.faces.carrier ∩ D.vertexCapsInRegion caps region R) ∩ ((caps p).face s).carrier := by
    ext q
    exact ⟨fun h => ⟨⟨h.1, hcap h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
  rw [heq, hbandCaps, union_inter_distrib_right]
  apply congrArg₂ (fun X Y : Set M => X ∪ Y)
  · by_cases hi : i = S.firstPiece
    · simp only [ite_and, if_pos hi,
        L.chordSegment_inter_cap hr hdisjoint huniqueL p s hsR]
    · simp only [ite_and, if_neg hi, empty_inter]
  · by_cases hi : i = S.lastPiece
    · simp only [ite_and, if_pos hi,
        T.chordSegment_inter_cap hr hdisjoint huniqueT p s hsR]
    · simp only [ite_and, if_neg hi, empty_inter]

theorem cap_band_face_coordinate_intersection
    (hr : r < 1)
    (hdisjoint : ∀ p q, p ≠ q → Disjoint (P p).carrier (P q).carrier)
    (hsector : ∀ p s, (P p).sector s ⊆ connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p s))
    (hclosed : ∀ p s, (P p).closedSector s ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p s)))
    (htrim : ∀ terminal, cut e terminal ∈ Ioo (0 : ℝ) 1)
    (hmatch : ∀ terminal, ∃ s t : Bool × Bool, ∃ k : Fin 3,
      s ≠ t ∧ (k = 1 ∨ k = 2) ∧ ∀ v, v = s ∨ v = t →
        (((caps (D.edgeEndpoint e terminal)).face v).boundary k).map 1 =
          D.edgeFromEndpoint e terminal (cut e terminal))
    (hbandCaps : B.faces.carrier ∩ D.vertexCapsInRegion caps region R =
      (if i = S.firstPiece then L.chordSegment r else ∅) ∪
        (if i = S.lastPiece then T.chordSegment r else ∅))
    (p : D.vertices) (s : Bool × Bool) (hsR : region p s = R)
    (j : Fin B.faces.interface.count × Bool) :
    CoordinateTriangleBoundaryIntersection ((caps p).coordinates s) (B.faces.faceCoordinates j)
      (rightTriangleBasis (caps p).scale_pos) (B.faces.faceBasis j) := by
  have huniqueL := L.tip_cap_unique hdisjoint hsector hclosed (htrim false) (hmatch false)
  have huniqueT := T.tip_cap_unique hdisjoint hsector hclosed (htrim true) (hmatch true)
  have hinter := K.band_inter_cap L T i B hr hdisjoint huniqueL huniqueT hbandCaps p s hsR
  have hendne : D.edgeEndpoint e false ≠ D.edgeEndpoint e true := by
    intro h
    have hm := congrArg Subtype.val h
    change (D.edge e.1 e.2).map 0 = (D.edge e.1 e.2).map 1 at hm
    have he := D.edge_injective e.1 e.2 (by simp) (by simp) hm
    norm_num at he
  have hr0 : 0 ≤ r := B.faces.left_length_pos.le
  by_cases hL : i = S.firstPiece ∧ p = D.edgeEndpoint e false ∧ s = L.sector
  · have hT : ¬(i = S.lastPiece ∧ p = D.edgeEndpoint e true ∧ s = T.sector) :=
      fun h => hendne (hL.2.1.symm.trans h.2.1)
    rw [if_pos hL, if_neg hT, union_empty] at hinter
    have hcut := K.first_leftCut_eq_chordSegment L T i B hL.1
    have hp := hL.2.1
    have hs := hL.2.2
    subst p s
    apply cap_band_coordinate_intersection_of_cut (caps (D.edgeEndpoint e false)) L.sector B.faces
      B.faces.leftCut (B.faces.firstCell, true) 2
      (B.faces.vertex (B.faces.firstCell.castSucc, false))
      (by rw [inter_comm, hinter, hcut]) B.faces.left_edge_image.symm
      (fun _ h => B.faces.outer_boundaries_subset_frontier (Or.inl (Or.inr h)))
      B.faces.face_inter_leftCut_subset_endpoint
      (c := if L.radialEdge = 1 then 1 else 0)
      (d := if L.radialEdge = 1 then 1 - r else r)
      (by split_ifs <;> simp)
      (by split_ifs <;> constructor <;> linarith)
      (hcut.trans (L.chordSegment_eq_subsegment hr0)) j
  by_cases hT : i = S.lastPiece ∧ p = D.edgeEndpoint e true ∧ s = T.sector
  · rw [if_neg hL, if_pos hT, empty_union] at hinter
    have hcut := K.last_rightCut_eq_chordSegment L T i B hT.1
    have hp := hT.2.1
    have hs := hT.2.2
    subst p s
    apply cap_band_coordinate_intersection_of_cut (caps (D.edgeEndpoint e true)) T.sector B.faces
      B.faces.rightCut (B.faces.lastCell, false) 0
      (B.faces.vertex (B.faces.lastCell.succ, true))
      (by rw [inter_comm, hinter, hcut]) B.faces.right_edge_image.symm
      (fun _ h => B.faces.outer_boundaries_subset_frontier (Or.inr h))
      B.faces.face_inter_rightCut_subset_endpoint
      (c := if T.radialEdge = 1 then 1 else 0)
      (d := if T.radialEdge = 1 then 1 - r else r)
      (by split_ifs <;> simp)
      (by split_ifs <;> constructor <;> linarith)
      (hcut.trans (T.chordSegment_eq_subsegment hr0)) j
  · rw [if_neg hL, if_neg hT, empty_union] at hinter
    apply CoordinateTriangleBoundaryIntersection.disjoint
    rw [← (caps p).carrier_eq, ← B.faces.face_carrier_eq_coordinates]
    exact (disjoint_iff_inter_eq_empty.mpr hinter).symm.mono_right
      (subset_iUnion (fun v => (B.faces.face v).carrier) j)

end OrientedEdgeGraphSubdivision.CutChain

end FiniteChartRegionDecomposition
end PoincareConjecture.Topology.Surface
