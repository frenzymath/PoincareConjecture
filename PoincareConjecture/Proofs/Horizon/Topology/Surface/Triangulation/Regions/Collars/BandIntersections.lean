


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Collars.Basic
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.CutGluing
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Meshes.CompatibleCover
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Bands.Coordinates









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Topology Manifold ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture.Topology.Surface

private theorem singleton_contact_mem_frontiers
    {M : Type*} [TopologicalSpace M]
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M) {A B : Set M}
    (hA : A ⊆ F.target) (hAr : closure (interior A) = A)
    (hBr : closure (interior B) = B) {q : M} (hq : q ∈ A ∩ B)
    (hpoint : A ∩ B ⊆ {q}) : q ∈ frontier A ∧ q ∈ frontier B := by
  have hd : Disjoint (interior A) (interior B) := by
    apply disjoint_left.mpr
    intro z hzA hzB
    have hopen := F.symm.isOpen_image_of_subset_source
      (isOpen_interior.inter isOpen_interior)
      (show interior A ∩ interior B ⊆ F.target from fun _ hz => hA (interior_subset hz.1))
    have hsub : F.symm '' (interior A ∩ interior B) ⊆ {F.symm q} := by
      rintro _ ⟨w, hw, rfl⟩
      exact congrArg F.symm (mem_singleton_iff.mp
        (hpoint ⟨interior_subset hw.1, interior_subset hw.2⟩))
    have h := hopen.subset_interior_iff.mpr hsub
    rw [interior_singleton] at h
    exact h ⟨z, ⟨hzA, hzB⟩, rfl⟩
  have hdA := hd.closure_right isOpen_interior
  have hdB := hd.closure_left isOpen_interior
  rw [hBr] at hdA
  rw [hAr] at hdB
  exact ⟨⟨subset_closure hq.1, fun h => disjoint_left.mp hdA h hq.2⟩,
    ⟨subset_closure hq.2, fun h => disjoint_left.mp hdB hq.1 h⟩⟩

private theorem coordinateTriangleBoundaryIntersection_of_face_contact
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    (f g : SmoothFace M)
    (F G : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (b c : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hf : f.carrier = F '' convexHull ℝ (range b))
    (hg : g.carrier = G '' convexHull ℝ (range c))
    (hff : frontier f.carrier = F '' frontier (convexHull ℝ (range b)))
    (hgf : frontier g.carrier = G '' frontier (convexHull ℝ (range c)))
    (hfb : ∀ k : Fin 3, (f.boundary k).map '' Icc (0 : ℝ) 1 =
      (F ∘ affineChartSegment (b (k.succAbove 0)) (b (k.succAbove 1))) '' Icc (0 : ℝ) 1)
    (hgb : ∀ k : Fin 3, (g.boundary k).map '' Icc (0 : ℝ) 1 =
      (G ∘ affineChartSegment (c (k.succAbove 0)) (c (k.succAbove 1))) '' Icc (0 : ℝ) 1)
    (h : (∃ k l : Fin 3, f.carrier ∩ g.carrier = (f.boundary k).map '' Icc (0 : ℝ) 1 ∧
        f.carrier ∩ g.carrier = (g.boundary l).map '' Icc (0 : ℝ) 1) ∨
      (∃ q, q ∈ frontier f.carrier ∧ q ∈ frontier g.carrier ∧ f.carrier ∩ g.carrier ⊆ {q}) ∨
      Disjoint f.carrier g.carrier) : CoordinateTriangleBoundaryIntersection F G b c := by
  rcases h with ⟨k, l, hk, hl⟩ | ⟨q, hq, hq', hsub⟩ | hd
  · apply CoordinateTriangleBoundaryIntersection.subsegment k l 0 1 0 1
      (by simp) (by simp) (by simp) (by simp)
    · simpa only [← hf, ← hg, uIcc_of_le zero_le_one, ← hfb k] using hk
    · simpa only [← hf, ← hg, uIcc_of_le zero_le_one, ← hgb l] using hl
  · exact .point q (hff ▸ hq) (hgf ▸ hq') (by simpa only [← hf, ← hg] using hsub)
  · exact .disjoint (by simpa only [← hf, ← hg] using hd)

namespace ObliqueBandFaces

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M}
  {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
  (B : ObliqueBandFaces F lo a b ua wa ub wb ra rb)

omit [T2Space M] in
private theorem rightCut_parameter {z : M} (hz : z ∈ B.rightCut) :
    (collarParameterEquiv (B.coordinates.symm z)).1 = 1 := by
  rw [← B.right_height_image] at hz
  obtain ⟨s, hs, rfl⟩ := hz
  have hband : collarParameterEquiv.symm (1, s) ∈ B.band := by
    rw [B.band_eq_subgraph]
    simpa only [mem_ofPred_eq, collarParameterEquiv.apply_symm_apply, mem_Icc] using
      And.intro (by simp : (1 : ℝ) ∈ Icc 0 1) hs
  rw [B.coordinates.left_inv (B.band_subset_source hband), collarParameterEquiv.apply_symm_apply]

omit [T2Space M] in
private theorem leftCut_parameter {z : M} (hz : z ∈ B.leftCut) :
    (collarParameterEquiv (B.coordinates.symm z)).1 = 0 := by
  rw [← B.left_height_image] at hz
  obtain ⟨s, hs, rfl⟩ := hz
  have hband : collarParameterEquiv.symm (0, s) ∈ B.band := by
    rw [B.band_eq_subgraph]
    simpa only [mem_ofPred_eq, collarParameterEquiv.apply_symm_apply, mem_Icc] using
      And.intro (by simp : (0 : ℝ) ∈ Icc 0 1) hs
  rw [B.coordinates.left_inv (B.band_subset_source hband), collarParameterEquiv.apply_symm_apply]

omit [T2Space M] in
private theorem cell_eq_last_of_one {i : Fin B.interface.count}
    (ht : (1 : ℝ) ∈ Icc (B.cut i.castSucc) (B.cut i.succ)) : i = B.lastCell := by
  have ho : B.cut i.succ = B.cut (Fin.last B.interface.count) := by
    rw [B.cut_last]
    exact le_antisymm (by simpa using B.cut_strictMono.monotone (Fin.le_last i.succ)) ht.2
  have hi := congrArg Fin.val (B.cut_strictMono.injective ho)
  apply Fin.ext
  dsimp [lastCell]
  simp only [Fin.val_succ, Fin.val_last] at hi
  omega

omit [T2Space M] in
private theorem cell_eq_first_of_zero {i : Fin B.interface.count}
    (ht : (0 : ℝ) ∈ Icc (B.cut i.castSucc) (B.cut i.succ)) : i = B.firstCell := by
  have hz : B.cut i.castSucc = B.cut 0 := by
    rw [B.cut_first]
    exact le_antisymm ht.1 (by simpa using B.cut_strictMono.monotone (Fin.zero_le i.castSucc))
  have hi := congrArg Fin.val (B.cut_strictMono.injective hz)
  exact Fin.ext hi

omit [T2Space M] in


theorem face_inter_rightCut_subset_endpoint
    (i : Fin B.interface.count × Bool) (hi : i ≠ (B.lastCell, false)) :
    (B.face i).carrier ∩ B.rightCut ⊆ {B.vertex (B.lastCell.succ, true)} := by
  rintro z ⟨hz, hcut⟩
  have hx := B.rightCut_parameter hcut
  have hparam := (B.pair i.1).parameter_mem hz
  have hlast : i.1 = B.lastCell := B.cell_eq_last_of_one (hx ▸ hparam.1)
  rcases i with ⟨i, side⟩
  dsimp at hlast
  subst i
  cases side
  · exact False.elim (hi rfl)
  · have hlast : B.lastCell.succ = Fin.last B.interface.count := by
      apply Fin.ext
      dsimp [lastCell]
      have hn := B.interface.count_pos
      omega
    have hz' := (B.pair B.lastCell).upper_right_vertex hz
      (by simpa only [hlast, B.cut_last] using hx)
    simpa only [vertex, ↓reduceIte, mem_singleton_iff,
      (B.upperGraph_endpoints B.lastCell).2] using hz'

omit [T2Space M] in


theorem face_inter_leftCut_subset_endpoint
    (i : Fin B.interface.count × Bool) (hi : i ≠ (B.firstCell, true)) :
    (B.face i).carrier ∩ B.leftCut ⊆ {B.vertex (B.firstCell.castSucc, false)} := by
  rintro z ⟨hz, hcut⟩
  have hx := B.leftCut_parameter hcut
  have hparam := (B.pair i.1).parameter_mem hz
  have hfirst : i.1 = B.firstCell := B.cell_eq_first_of_zero (hx ▸ hparam.1)
  rcases i with ⟨i, side⟩
  dsimp at hfirst
  subst i
  cases side
  · have hfirst : B.firstCell.castSucc = 0 := rfl
    have hz' := (B.pair B.firstCell).lower_left_vertex hz
      (by simpa only [hfirst, B.cut_first] using hx)
    exact hz'
  · exact False.elim (hi rfl)

variable {G : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M}
  {lo' : ℝ → ℝ} {a' b' ua' wa' ub' wb' ra' rb' : ℝ}
  (B' : ObliqueBandFaces G lo' a' b' ua' wa' ub' wb' ra' rb')



theorem endpoint_faces_intersection_of_shared_cut
    (hinter : B.carrier ∩ B'.carrier = B.rightCut) (hcut : B.rightCut = B'.leftCut) :
    (B.pair B.lastCell).lower.carrier ∩ (B'.pair B'.firstCell).upper.carrier = B.rightCut ∧
    (B.pair B.lastCell).lower.carrier ∩ (B'.pair B'.firstCell).upper.carrier =
      ((B.pair B.lastCell).lower.boundary 0).map '' Icc (0 : ℝ) 1 ∧
    (B.pair B.lastCell).lower.carrier ∩ (B'.pair B'.firstCell).upper.carrier =
      ((B'.pair B'.firstCell).upper.boundary 2).map '' Icc (0 : ℝ) 1 := by
  have heq : (B.pair B.lastCell).lower.carrier ∩
      (B'.pair B'.firstCell).upper.carrier = B.rightCut := by
    apply subset_antisymm
    · rw [← hinter]
      exact inter_subset_inter
        (subset_iUnion (fun i => (B.face i).carrier) (B.lastCell, false))
        (subset_iUnion (fun i => (B'.face i).carrier) (B'.firstCell, true))
    · intro q hq
      constructor
      · exact (B.pair B.lastCell).lower.isClosed_carrier.frontier_subset
          ((B.pair B.lastCell).lower.boundary_image_subset_frontier 0
            (B.right_edge_image.symm ▸ hq))
      · have hq' : q ∈ B'.leftCut := hcut ▸ hq
        exact (B'.pair B'.firstCell).upper.isClosed_carrier.frontier_subset
          ((B'.pair B'.firstCell).upper.boundary_image_subset_frontier 2
            (B'.left_edge_image.symm ▸ hq'))
  exact ⟨heq, heq.trans B.right_edge_image.symm, heq.trans (hcut.trans B'.left_edge_image.symm)⟩




theorem face_intersection_of_shared_endpoint_cut
    (hinter : B.carrier ∩ B'.carrier = B.rightCut) (hcut : B.rightCut = B'.leftCut)
    (i : Fin B.interface.count × Bool) (j : Fin B'.interface.count × Bool) :
    (∃ k l : Fin 3,
      (B.face i).carrier ∩ (B'.face j).carrier =
        ((B.face i).boundary k).map '' Icc (0 : ℝ) 1 ∧
      (B.face i).carrier ∩ (B'.face j).carrier =
        ((B'.face j).boundary l).map '' Icc (0 : ℝ) 1) ∨
    (∃ q : M, q ∈ frontier (B.face i).carrier ∧ q ∈ frontier (B'.face j).carrier ∧
      (B.face i).carrier ∩ (B'.face j).carrier ⊆ {q}) ∨
    Disjoint (B.face i).carrier (B'.face j).carrier := by
  have hsub : (B.face i).carrier ∩ (B'.face j).carrier ⊆ B.rightCut := by
    rw [← hinter]
    exact inter_subset_inter (subset_iUnion (fun i => (B.face i).carrier) i)
      (subset_iUnion (fun j => (B'.face j).carrier) j)
  have hfront (q : M) (hq : q ∈ (B.face i).carrier ∩ (B'.face j).carrier) :
      q ∈ frontier (B.face i).carrier ∧ q ∈ frontier (B'.face j).carrier := by
    have hB : q ∈ frontier B.carrier := B.outer_boundaries_subset_frontier (Or.inr (hsub hq))
    have hB' : q ∈ frontier B'.carrier :=
      B'.outer_boundaries_subset_frontier (Or.inl (Or.inr (hcut ▸ hsub hq)))
    exact ⟨⟨subset_closure hq.1, fun h => hB.2 (interior_mono (subset_iUnion _ i) h)⟩,
      ⟨subset_closure hq.2, fun h => hB'.2 (interior_mono (subset_iUnion _ j) h)⟩⟩
  by_cases hi : i = (B.lastCell, false)
  · by_cases hj : j = (B'.firstCell, true)
    · subst i j
      exact Or.inl ⟨0, 2, (B.endpoint_faces_intersection_of_shared_cut B' hinter hcut).2⟩
    · have hpoint : (B.face i).carrier ∩ (B'.face j).carrier ⊆
          {B'.vertex (B'.firstCell.castSucc, false)} :=
        fun _ hq => B'.face_inter_leftCut_subset_endpoint j hj ⟨hq.2, hcut ▸ hsub hq⟩
      by_cases hnonempty : ((B.face i).carrier ∩ (B'.face j).carrier).Nonempty
      · obtain ⟨q, hq⟩ := hnonempty
        exact Or.inr (Or.inl ⟨q, (hfront q hq).1, (hfront q hq).2,
          fun z hz => (mem_singleton_iff.mp (hpoint hz)).trans
            (mem_singleton_iff.mp (hpoint hq)).symm⟩)
      · exact Or.inr (Or.inr (disjoint_iff_inter_eq_empty.mpr
          (not_nonempty_iff_eq_empty.mp hnonempty)))
  · have hpoint : (B.face i).carrier ∩ (B'.face j).carrier ⊆
        {B.vertex (B.lastCell.succ, true)} :=
      fun _ hq => B.face_inter_rightCut_subset_endpoint i hi ⟨hq.1, hsub hq⟩
    by_cases hnonempty : ((B.face i).carrier ∩ (B'.face j).carrier).Nonempty
    · obtain ⟨q, hq⟩ := hnonempty
      exact Or.inr (Or.inl ⟨q, (hfront q hq).1, (hfront q hq).2,
        fun z hz => (mem_singleton_iff.mp (hpoint hz)).trans
          (mem_singleton_iff.mp (hpoint hq)).symm⟩)
    · exact Or.inr (Or.inr (disjoint_iff_inter_eq_empty.mpr
        (not_nonempty_iff_eq_empty.mp hnonempty)))



theorem face_coordinate_intersection
    (i j : Fin B.interface.count × Bool) (hij : i ≠ j) :
    CoordinateTriangleBoundaryIntersection (B.faceCoordinates i) (B.faceCoordinates j)
      (B.faceBasis i) (B.faceBasis j) := by
  apply coordinateTriangleBoundaryIntersection_of_face_contact
    (B.face i) (B.face j) _ _ _ _
    (B.face_carrier_eq_coordinates i) (B.face_carrier_eq_coordinates j)
    (B.face_frontier_eq_coordinates i) (B.face_frontier_eq_coordinates j)
    (B.face_boundary_image i) (B.face_boundary_image j)
  rcases B.face_intersection i j hij with ⟨k, l, hedge, hinter⟩ | ⟨v, hv⟩
  · exact Or.inl ⟨k, l, hinter, hinter.trans
      (congrArg (fun e : SmoothEdge M => e.map '' Icc (0 : ℝ) 1) hedge)⟩
  · by_cases hnonempty : ((B.face i).carrier ∩ (B.face j).carrier).Nonempty
    · obtain ⟨q, hq⟩ := hnonempty
      have hpoint : (B.face i).carrier ∩ (B.face j).carrier ⊆ {q} :=
        fun _ hz => (mem_singleton_iff.mp (hv hz)).trans (mem_singleton_iff.mp (hv hq)).symm
      have hregular (i : Fin B.interface.count × Bool) :
          closure (interior (B.face i).carrier) = (B.face i).carrier := by
        rw [B.face_carrier_eq_coordinates i]
        exact coordinate_triangle_closure_interior _ _ (B.face_triangle_subset_source i)
      have hfront := singleton_contact_mem_frontiers B.coordinates
        ((subset_iUnion (fun i => (B.face i).carrier) i).trans B.carrier_subset_target)
        (hregular i) (hregular j) hq hpoint
      exact Or.inr (Or.inl ⟨q, hfront.1, hfront.2, hpoint⟩)
    · exact Or.inr (Or.inr (disjoint_iff_inter_eq_empty.mpr
        (not_nonempty_iff_eq_empty.mp hnonempty)))

end ObliqueBandFaces

namespace FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {D : FiniteChartRegionDecomposition (M := M)} {e : D.EdgeIndex} {R : D.regions}
  {C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M} {a b : ℝ}

namespace OrientedEdgeGraphSubdivision.CutChain

variable {S : D.OrientedEdgeGraphSubdivision e R C a b}
  {dLeft dRight : EuclideanSpace ℝ (Fin 2)} (K : S.CutChain dLeft dRight)
  {δ r : ℝ}
  (B : ∀ i : Fin S.count, (S.piece i).FixedStripBandFaces (K.graphCuts i) δ r r)



theorem adjacent_faces_intersection (i j : Fin S.count) (hij : i.succ = j.castSucc)
    (hseparate : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ z w : ℝ, |z| < δ → |w| < δ →
        (S.piece i).strip (K.graphCuts i) (t, z) =
          (S.piece j).strip (K.graphCuts j) (s, w) → t = 1 ∧ s = 0)
    (v : Fin (B i).faces.interface.count × Bool)
    (w : Fin (B j).faces.interface.count × Bool) :
    (∃ k l : Fin 3,
      ((B i).faces.face v).carrier ∩ ((B j).faces.face w).carrier =
        (((B i).faces.face v).boundary k).map '' Icc (0 : ℝ) 1 ∧
      ((B i).faces.face v).carrier ∩ ((B j).faces.face w).carrier =
        (((B j).faces.face w).boundary l).map '' Icc (0 : ℝ) 1) ∨
    (∃ q : M, q ∈ frontier ((B i).faces.face v).carrier ∧
      q ∈ frontier ((B j).faces.face w).carrier ∧
      ((B i).faces.face v).carrier ∩ ((B j).faces.face w).carrier ⊆ {q}) ∨
    Disjoint ((B i).faces.face v).carrier ((B j).faces.face w).carrier := by
  have hinter : (B i).faces.carrier ∩ (B j).faces.carrier = (B i).faces.rightCut := by
    rw [K.adjacent_band_intersection B i j hij hseparate, (B i).rightCut_eq_segment (S.cut_lt i).le]
    simp only [Prod.eta, ContinuousLinearEquiv.symm_apply_apply]
  have hcut : (B i).faces.rightCut = (B j).faces.leftCut := by
    have h := K.adjacent_endpointEdge_image B i j hij
    simpa only [ObliqueBandFaces.endpointEdge_image, ↓reduceIte, Bool.false_eq_true] using h
  exact (B i).faces.face_intersection_of_shared_endpoint_cut (B j).faces hinter hcut v w

end OrientedEdgeGraphSubdivision.CutChain

variable (D)
  (chart : D.regions → D.centers) (cut : D.EdgeIndex → Bool → ℝ)
  (S : ∀ p : D.IncidentEdgeIndex,
    D.OrientedEdgeGraphSubdivision p.1.2 p.1.1
      (chartAt (EuclideanSpace ℝ (Fin 2)) (chart p.1.1 : M)).symm
      (cut p.1.2 false) (1 - cut p.1.2 true))
  {dLeft dRight : D.IncidentEdgeIndex → EuclideanSpace ℝ (Fin 2)}
  (K : ∀ p, (S p).CutChain (dLeft p) (dRight p)) {δ r : ℝ}
  (B : ∀ p i, ((S p).piece i).FixedStripBandFaces ((K p).graphCuts i) δ r r)

omit [T2Space M] in


theorem separated_graph_band_faces_disjoint
    (hseparate : ∀ i j : D.IncidentGraphPieceIndex chart cut S,
      D.IncidentGraphPiecesSeparated chart cut S i j → Disjoint
        (((S i.1).piece i.2).strip ((K i.1).graphCuts i.2) '' (Icc (0 : ℝ) 1 ×ˢ Ioo (-δ) δ))
        (((S j.1).piece j.2).strip ((K j.1).graphCuts j.2) '' (Icc (0 : ℝ) 1 ×ˢ Ioo (-δ) δ)))
    (i j : D.IncidentGraphPieceIndex chart cut S)
    (hij : D.IncidentGraphPiecesSeparated chart cut S i j)
    (v : Fin (B i.1 i.2).faces.interface.count × Bool)
    (w : Fin (B j.1 j.2).faces.interface.count × Bool) :
    Disjoint ((B i.1 i.2).faces.face v).carrier ((B j.1 j.2).faces.face w).carrier :=
  (hseparate i j hij).mono
    ((subset_iUnion (fun v => ((B i.1 i.2).faces.face v).carrier) v).trans
      (B i.1 i.2).carrier_subset_open_strip)
    ((subset_iUnion (fun w => ((B j.1 j.2).faces.face w).carrier) w).trans
      (B j.1 j.2).carrier_subset_open_strip)




theorem incident_band_faces_intersection
    (hadjacent : ∀ p (i j : Fin (S p).count), i.succ = j.castSucc →
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
        ∀ z w : ℝ, |z| < δ → |w| < δ →
          ((S p).piece i).strip ((K p).graphCuts i) (t, z) =
            ((S p).piece j).strip ((K p).graphCuts j) (s, w) → t = 1 ∧ s = 0)
    (hseparate : ∀ i j : D.IncidentGraphPieceIndex chart cut S,
      D.IncidentGraphPiecesSeparated chart cut S i j → Disjoint
        (((S i.1).piece i.2).strip ((K i.1).graphCuts i.2) '' (Icc (0 : ℝ) 1 ×ˢ Ioo (-δ) δ))
        (((S j.1).piece j.2).strip ((K j.1).graphCuts j.2) '' (Icc (0 : ℝ) 1 ×ˢ Ioo (-δ) δ)))
    (i j : D.IncidentGraphPieceIndex chart cut S) (hne : i ≠ j)
    (hregion : i.1.1.1 = j.1.1.1)
    (v : Fin (B i.1 i.2).faces.interface.count × Bool)
    (w : Fin (B j.1 j.2).faces.interface.count × Bool) :
    (∃ k l : Fin 3,
      ((B i.1 i.2).faces.face v).carrier ∩ ((B j.1 j.2).faces.face w).carrier =
        (((B i.1 i.2).faces.face v).boundary k).map '' Icc (0 : ℝ) 1 ∧
      ((B i.1 i.2).faces.face v).carrier ∩ ((B j.1 j.2).faces.face w).carrier =
        (((B j.1 j.2).faces.face w).boundary l).map '' Icc (0 : ℝ) 1) ∨
    (∃ q : M, q ∈ frontier ((B i.1 i.2).faces.face v).carrier ∧
      q ∈ frontier ((B j.1 j.2).faces.face w).carrier ∧
      ((B i.1 i.2).faces.face v).carrier ∩ ((B j.1 j.2).faces.face w).carrier ⊆ {q}) ∨
    Disjoint ((B i.1 i.2).faces.face v).carrier ((B j.1 j.2).faces.face w).carrier := by
  by_cases he : i.1.1.2 = j.1.1.2
  · have hp : i.1 = j.1 := Subtype.ext (Prod.ext hregion he)
    rcases i with ⟨p, i⟩
    rcases j with ⟨q, j⟩
    dsimp at hp
    subst q
    have hij : i ≠ j := fun h => hne (h ▸ rfl)
    by_cases hnext : i.succ = j.castSucc
    · exact (K p).adjacent_faces_intersection (B p) i j hnext (hadjacent p i j hnext) v w
    by_cases hprev : j.succ = i.castSucc
    · rcases (K p).adjacent_faces_intersection (B p) j i hprev (hadjacent p j i hprev) w v
        with ⟨k, l, hk, hl⟩ | ⟨z, hz, hz', hpoint⟩ | hdisjoint
      · exact Or.inl ⟨l, k, by rw [inter_comm]; exact hl, by rw [inter_comm]; exact hk⟩
      · exact Or.inr (Or.inl ⟨z, hz', hz, by rwa [inter_comm]⟩)
      · exact Or.inr (Or.inr hdisjoint.symm)
    have hgap : i.val + 1 < j.val ∨ j.val + 1 < i.val := by
      have hneval : i.val ≠ j.val := fun h => hij (Fin.ext h)
      have hn : i.val + 1 ≠ j.val := fun h => hnext (Fin.ext h)
      have hp : j.val + 1 ≠ i.val := fun h => hprev (Fin.ext h)
      omega
    exact Or.inr (Or.inr (D.separated_graph_band_faces_disjoint chart cut S K B hseparate
      ⟨p, i⟩ ⟨p, j⟩ (Or.inr ⟨rfl, hgap⟩) v w))
  · exact Or.inr (Or.inr (D.separated_graph_band_faces_disjoint chart cut S K B hseparate
      i j (Or.inl he) v w))



theorem incident_band_faces_coordinate_intersection
    (hadjacent : ∀ p (i j : Fin (S p).count), i.succ = j.castSucc →
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
        ∀ z w : ℝ, |z| < δ → |w| < δ →
          ((S p).piece i).strip ((K p).graphCuts i) (t, z) =
            ((S p).piece j).strip ((K p).graphCuts j) (s, w) → t = 1 ∧ s = 0)
    (hseparate : ∀ i j : D.IncidentGraphPieceIndex chart cut S,
      D.IncidentGraphPiecesSeparated chart cut S i j → Disjoint
        (((S i.1).piece i.2).strip ((K i.1).graphCuts i.2) '' (Icc (0 : ℝ) 1 ×ˢ Ioo (-δ) δ))
        (((S j.1).piece j.2).strip ((K j.1).graphCuts j.2) '' (Icc (0 : ℝ) 1 ×ˢ Ioo (-δ) δ)))
    (i j : D.IncidentGraphPieceIndex chart cut S) (hne : i ≠ j)
    (hregion : i.1.1.1 = j.1.1.1)
    (v : Fin (B i.1 i.2).faces.interface.count × Bool)
    (w : Fin (B j.1 j.2).faces.interface.count × Bool) :
    CoordinateTriangleBoundaryIntersection
      ((B i.1 i.2).faces.faceCoordinates v) ((B j.1 j.2).faces.faceCoordinates w)
      ((B i.1 i.2).faces.faceBasis v) ((B j.1 j.2).faces.faceBasis w) :=
  coordinateTriangleBoundaryIntersection_of_face_contact
    ((B i.1 i.2).faces.face v) ((B j.1 j.2).faces.face w) _ _ _ _
    ((B i.1 i.2).faces.face_carrier_eq_coordinates v)
    ((B j.1 j.2).faces.face_carrier_eq_coordinates w)
    ((B i.1 i.2).faces.face_frontier_eq_coordinates v)
    ((B j.1 j.2).faces.face_frontier_eq_coordinates w)
    ((B i.1 i.2).faces.face_boundary_image v)
    ((B j.1 j.2).faces.face_boundary_image w)
    (D.incident_band_faces_intersection chart cut S K B hadjacent hseparate i j hne hregion v w)

end FiniteChartRegionDecomposition
end PoincareConjecture.Topology.Surface
