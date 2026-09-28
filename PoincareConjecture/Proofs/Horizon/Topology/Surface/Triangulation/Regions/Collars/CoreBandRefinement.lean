import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Collars.CoreBandContacts
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Bands.Coordinates
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Meshes.ConnectedIntersections

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Topology Manifold ContDiff
open Poincare.Topology.Plane.Curves Poincare.Topology.Plane.Meshes

namespace PoincareConjecture.Topology.Surface

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

namespace ObliqueBandFaces

variable {F : OpenPartialHomeomorph Plane M} {lo : ℝ → ℝ}
  {a b ua wa ub wb ra rb : ℝ} (B : ObliqueBandFaces F lo a b ua wa ub wb ra rb)

include B in
omit [T2Space M] in
theorem right_segment_subset_source :
    collarParameterEquiv.symm '' segment ℝ (b, lo b) (b + rb * ub, lo b + rb * wb) ⊆ F.source := by
  rintro z ⟨q, hq, rfl⟩
  have he : (b + rb * ub, lo b + rb * wb) = (b, lo b) + rb • (ub, wb) := by
    ext <;> simp [smul_eq_mul]
  rw [he, ← B.cuts.right.inverse_ray_image_Icc (b, lo b) (ub, wb)
    B.right_length_pos.le B.interface.right_parameter_mem] at hq
  obtain ⟨h, hh, rfl⟩ := hq
  have htarget : h ∈ B.cuts.right.parameter.target := by
    rw [← B.cuts.right.parameter_image_Icc B.right_length_pos.le B.interface.right_parameter_mem] at hh
    obtain ⟨v, hv, rfl⟩ := hh
    exact B.cuts.right.parameter.map_source
      (B.cuts.right.parameter_Icc_subset_source B.interface.right_parameter_mem hv)
  have hband : collarParameterEquiv.symm (1, h) ∈ B.band := by
    rw [B.band_eq_subgraph]
    simp only [mem_ofPred_eq, collarParameterEquiv.apply_symm_apply]
    exact ⟨by simp, hh.1, B.height_one.symm ▸ hh.2⟩
  have hs := (B.band_subset_source hband).2
  change collarParameterEquiv.symm
    (B.cuts.coordinates B.open_domain B.smooth_lower
      (collarParameterEquiv (collarParameterEquiv.symm (1, h)))) ∈ F.source at hs
  rw [collarParameterEquiv.apply_symm_apply, B.cuts.coordinates_apply, obliqueStripMap_right,
    B.cuts.right.line_identity htarget] at hs
  exact hs

omit [T2Space M] in
theorem top_vertex_eq_upper_endpoint (i : Fin B.interface.count) :
    B.vertex (i.succ, true) = ((B.pair i).upper.boundary 0).map 1 := by
  rw [(B.pair i).upper_edge]
  simp only [one_mul, add_sub_cancel, vertex, if_true]
  change B.coordinates (collarParameterEquiv.symm (B.cut i.succ, B.interface.height i.succ)) =
    B.coordinates (collarParameterEquiv.symm (B.cut i.succ, B.upperGraph i (B.cut i.succ)))
  rw [(B.upperGraph_endpoints i).2]

omit [T2Space M] in
theorem top_vertex_eq_lower_endpoint (i : Fin B.interface.count) :
    B.vertex (i.succ, true) = ((B.pair i).lower.boundary 0).map 1 := by
  rw [(B.pair i).right_edge]
  simp only [sub_zero, one_mul, zero_add, vertex, if_true]
  change B.coordinates (collarParameterEquiv.symm (B.cut i.succ, B.interface.height i.succ)) =
    B.coordinates (collarParameterEquiv.symm (B.cut i.succ, B.upperGraph i (B.cut i.succ)))
  rw [(B.upperGraph_endpoints i).2]

end ObliqueBandFaces

namespace FiniteChartRegionDecomposition.OrientedGraphPiece.FixedStripBandFaces

variable {D : FiniteChartRegionDecomposition (M := M)} {e : D.EdgeIndex} {R : D.regions}
  {C : OpenPartialHomeomorph Plane M} {a b : ℝ}
  {G : D.OrientedGraphPiece e R C a b} {ua wa ub wb : ℝ}
  {P : TransverseGraphCuts G.lower (G.parameter a) (G.parameter b) ua wa ub wb}
  {δ ra rb : ℝ} (B : G.FixedStripBandFaces P δ ra rb)

noncomputable def chartTopVertex (i : Fin (B.faces.interface.count + 1)) : Plane :=
  G.frame.symm (B.faces.interface.cut i,
    G.lower (B.faces.interface.cut i) + B.faces.interface.height i)

noncomputable def chartRightBase (_B : G.FixedStripBandFaces P δ ra rb) : Plane :=
  G.frame.symm (G.parameter b, G.lower (G.parameter b))

noncomputable def chartRightTip (_B : G.FixedStripBandFaces P δ ra rb) : Plane :=
  G.frame.symm (G.parameter b + rb * ub, G.lower (G.parameter b) + rb * wb)

omit [T2Space M] in
private theorem image_linear_chart_segment (p q : ℝ × ℝ) :
    (fun z => linearGraphCoordinates C G.frame (collarParameterEquiv.symm z)) ''
      segment ℝ p q = C '' segment ℝ (G.frame.symm p) (G.frame.symm q) := by
  have he : (fun z => linearGraphCoordinates C G.frame (collarParameterEquiv.symm z)) =
      C ∘ G.frame.symm := by
    funext z
    rw [linearGraphCoordinates_apply, collarParameterEquiv.apply_symm_apply]
    rfl
  rw [he]
  change (fun z => C (G.frame.symm z)) '' segment ℝ p q = _
  rw [← image_image (g := C) (f := G.frame.symm)]
  exact congrArg (fun S => C '' S)
    (image_segment ℝ G.frame.symm.toLinearMap.toAffineMap p q)

omit [T2Space M] in
private theorem frame_image_segment (p q : ℝ × ℝ) :
    G.frame.symm '' segment ℝ p q = segment ℝ (G.frame.symm p) (G.frame.symm q) :=
  image_segment ℝ G.frame.symm.toLinearMap.toAffineMap p q

omit [T2Space M] in
theorem chartTopSegment_image (i : Fin B.faces.interface.count) :
    C '' segment ℝ (B.chartTopVertex i.castSucc) (B.chartTopVertex i.succ) =
      ((B.faces.pair i).upper.boundary 0).map '' Icc (0 : ℝ) 1 := by
  rw [B.faces.upper_edge_image, image_linear_chart_segment]
  rfl

omit [T2Space M] in
theorem chartRightSegment_image :
    C '' segment ℝ B.chartRightBase B.chartRightTip =
      ((B.faces.pair B.faces.lastCell).lower.boundary 0).map '' Icc (0 : ℝ) 1 := by
  rw [B.faces.right_edge_image, image_linear_chart_segment]
  rfl

omit [T2Space M] in
theorem chartTopSegment_subset_source (i : Fin B.faces.interface.count) :
    segment ℝ (B.chartTopVertex i.castSucc) (B.chartTopVertex i.succ) ⊆ C.source := by
  have hs := B.faces.upper_segment_subset_source i
  have himage := frame_image_segment (G := G)
    (B.faces.interface.cut i.castSucc,
      G.lower (B.faces.interface.cut i.castSucc) + B.faces.interface.height i.castSucc)
    (B.faces.interface.cut i.succ,
      G.lower (B.faces.interface.cut i.succ) + B.faces.interface.height i.succ)
  change segment ℝ (G.frame.symm _) (G.frame.symm _) ⊆ C.source
  rw [← himage]
  rintro z ⟨q, hq, rfl⟩
  have h := (hs ⟨q, hq, rfl⟩).2
  change G.frame.symm (collarParameterEquiv (collarParameterEquiv.symm q)) ∈ C.source at h
  simpa only [collarParameterEquiv.apply_symm_apply] using h

omit [T2Space M] in
theorem chartRightSegment_subset_source :
    segment ℝ B.chartRightBase B.chartRightTip ⊆ C.source := by
  have hs := B.faces.right_segment_subset_source
  have himage := frame_image_segment (G := G)
    (G.parameter b, G.lower (G.parameter b))
    (G.parameter b + rb * ub, G.lower (G.parameter b) + rb * wb)
  change segment ℝ (G.frame.symm _) (G.frame.symm _) ⊆ C.source
  rw [← himage]
  rintro z ⟨q, hq, rfl⟩
  have h := (hs ⟨q, hq, rfl⟩).2
  change G.frame.symm (collarParameterEquiv (collarParameterEquiv.symm q)) ∈ C.source at h
  simpa only [collarParameterEquiv.apply_symm_apply] using h

noncomputable def topSupportingLine (i : Fin B.faces.interface.count) : Plane →ᵃ[ℝ] ℝ :=
  Classical.choose (Poincare.Topology.Plane.exists_affine_line_containing_segment
    (B.chartTopVertex i.castSucc) (B.chartTopVertex i.succ))

noncomputable def rightSupportingLine : Plane →ᵃ[ℝ] ℝ :=
  Classical.choose (Poincare.Topology.Plane.exists_affine_line_containing_segment
    B.chartRightBase B.chartRightTip)

omit [T2Space M] in
theorem topSupportingLine_spec (i : Fin B.faces.interface.count) :
    Function.Surjective (B.topSupportingLine i) ∧
      segment ℝ (B.chartTopVertex i.castSucc) (B.chartTopVertex i.succ) ⊆
        {z | B.topSupportingLine i z = 0} :=
  Classical.choose_spec (Poincare.Topology.Plane.exists_affine_line_containing_segment _ _)

omit [T2Space M] in
theorem rightSupportingLine_spec : Function.Surjective B.rightSupportingLine ∧
    segment ℝ B.chartRightBase B.chartRightTip ⊆ {z | B.rightSupportingLine z = 0} :=
  Classical.choose_spec (Poincare.Topology.Plane.exists_affine_line_containing_segment _ _)

noncomputable def coreContactLines : List (Plane →ᵃ[ℝ] ℝ) :=
  [cornerSeparator B.firstUpperChartBasis, B.firstUpperChartBasis.coord 1,
    B.firstUpperChartBasis.coord 2, B.rightSupportingLine] ++ List.ofFn B.topSupportingLine

private theorem coreContact_of_convex_edge (T : TriangleMesh) (t : T.Triangle)
    (hsource : T.toPlaneComplex.support ⊆ C.source)
    (i : Fin B.faces.interface.count × Bool) (j : Fin 3)
    (A : Set Plane) (hA : A ⊆ C.source) (hconvex : Convex ℝ A)
    (hedge : C '' A ⊆ ((B.faces.face i).boundary j).map '' Icc (0 : ℝ) 1)
    (hcontact : (C '' convexHull ℝ (range (meshTriangleBasis T t))) ∩
      (B.faces.face i).carrier ⊆ C '' A)
    (l : Plane →ᵃ[ℝ] ℝ) (hsurj : Function.Surjective l)
    (hmono : T.IsMonochromatic l) (hzero : A ⊆ {z | l z = 0}) :
    CoordinateTriangleBoundaryIntersection C (B.faces.faceCoordinates i)
      (meshTriangleBasis T t) (B.faces.faceBasis i) := by
  have hK : convexHull ℝ (range (meshTriangleBasis T t)) ⊆ C.source :=
    (meshTriangleBasis_subset_support T t).trans hsource
  have hAP : C '' A ⊆ (B.faces.face i).carrier :=
    hedge.trans (((B.faces.face i).boundary_image_subset_frontier j).trans
      (B.faces.face i).isClosed_carrier.frontier_subset)
  have heq : (C '' convexHull ℝ (range (meshTriangleBasis T t))) ∩
      (B.faces.face i).carrier = C '' (convexHull ℝ (range (meshTriangleBasis T t)) ∩ A) := by
    apply subset_antisymm
    · rintro y ⟨⟨z, hz, rfl⟩, hp⟩
      obtain ⟨w, hw, hwz⟩ := hcontact ⟨mem_image_of_mem C hz, hp⟩
      have hwz' := C.injOn (hA hw) (hK hz) hwz
      subst w
      exact ⟨z, ⟨hz, hw⟩, rfl⟩
    · rintro y ⟨z, ⟨hz, ha⟩, rfl⟩
      exact ⟨mem_image_of_mem C hz, hAP (mem_image_of_mem C ha)⟩
  have hside : (∀ k, 0 ≤ l (meshTriangleBasis T t k)) ∨
      (∀ k, l (meshTriangleBasis T t k) ≤ 0) := by
    have hvertices (k : Fin 3) : meshTriangleBasis T t k ∈ T.triangleCarrier t.1 := by
      change _ ∈ convexHull ℝ (T.position '' (t.1 : Set T.Vertex))
      rw [← range_meshTriangleBasis]
      exact subset_convexHull ℝ _ (mem_range_self _)
    rcases hmono.triangleCarrier_halfspace T t with hpos | hneg
    · exact Or.inl (fun k => hpos _ (hvertices k))
    · exact Or.inr (fun k => hneg _ (hvertices k))
  apply CoordinateTriangleBoundaryIntersection.of_convex_chart_contact C
    (B.faces.faceCoordinates i) (meshTriangleBasis T t) (B.faces.faceBasis i)
    hK (B.faces.face_triangle_subset_source i) A hconvex
    (by simpa only [← B.faces.face_carrier_eq_coordinates i] using heq) l hsurj hside hzero j
  rw [← B.faces.face_carrier_eq_coordinates i]
  have hcanonical : ((B.faces.face i).boundary j).map '' Icc (0 : ℝ) 1 =
      B.faces.faceCoordinates i '' affineSegment ℝ
        (B.faces.faceBasis i (j.succAbove 0)) (B.faces.faceBasis i (j.succAbove 1)) := by
    rw [B.faces.face_boundary_image]
    have himage (p q : Plane) : affineChartSegment p q '' Icc (0 : ℝ) 1 =
        affineSegment ℝ p q := by
      unfold affineSegment
      congr 1
      funext u
      simp [affineChartSegment, AffineMap.lineMap_apply, add_comm]
    rw [← himage, image_image]
    rfl
  exact hcontact.trans (hedge.trans hcanonical.subset)

private theorem upper_contact_of_monochromatic (T : TriangleMesh) (t : T.Triangle)
    (hsource : T.toPlaneComplex.support ⊆ C.source)
    (hinterior : Disjoint (C '' T.toPlaneComplex.support) (interior B.faces.carrier))
    (hlower : Disjoint (C '' T.toPlaneComplex.support) B.faces.lowerArc)
    (i : Fin B.faces.interface.count) (hi : i ≠ B.faces.firstCell)
    (hmono : T.IsMonochromatic (B.topSupportingLine i)) :
    CoordinateTriangleBoundaryIntersection C (B.faces.faceCoordinates (i, true))
      (meshTriangleBasis T t) (B.faces.faceBasis (i, true)) := by
  apply B.coreContact_of_convex_edge T t hsource (i, true) 0
    (segment ℝ (B.chartTopVertex i.castSucc) (B.chartTopVertex i.succ))
    (B.chartTopSegment_subset_source i) (convex_segment _ _) ?_ ?_
    (B.topSupportingLine i) (B.topSupportingLine_spec i).1 hmono (B.topSupportingLine_spec i).2
  · exact (B.chartTopSegment_image i).subset
  · rw [B.chartTopSegment_image i]
    exact (inter_subset_inter_left _ (image_mono (meshTriangleBasis_subset_support T t))).trans
      (B.faces.upper_carrier_inter_subset_upper_edge hinterior hlower hi)

private theorem right_contact_of_monochromatic (T : TriangleMesh) (t : T.Triangle)
    (hsource : T.toPlaneComplex.support ⊆ C.source)
    (hinterior : Disjoint (C '' T.toPlaneComplex.support) (interior B.faces.carrier))
    (hlower : Disjoint (C '' T.toPlaneComplex.support) B.faces.lowerArc)
    (hmono : T.IsMonochromatic B.rightSupportingLine) :
    CoordinateTriangleBoundaryIntersection C (B.faces.faceCoordinates (B.faces.lastCell, false))
      (meshTriangleBasis T t) (B.faces.faceBasis (B.faces.lastCell, false)) := by
  apply B.coreContact_of_convex_edge T t hsource (B.faces.lastCell, false) 0
    (segment ℝ B.chartRightBase B.chartRightTip) B.chartRightSegment_subset_source
    (convex_segment _ _) B.chartRightSegment_image.subset ?_
    B.rightSupportingLine B.rightSupportingLine_spec.1 hmono B.rightSupportingLine_spec.2
  rw [B.chartRightSegment_image]
  rw [B.faces.right_edge_image]
  exact (inter_subset_inter_left _ (image_mono (meshTriangleBasis_subset_support T t))).trans
    (B.faces.last_lower_carrier_inter_subset_rightCut hinterior hlower)

private theorem lower_contact_of_monochromatic (T : TriangleMesh) (t : T.Triangle)
    (hsource : T.toPlaneComplex.support ⊆ C.source)
    (hinterior : Disjoint (C '' T.toPlaneComplex.support) (interior B.faces.carrier))
    (hlower : Disjoint (C '' T.toPlaneComplex.support) B.faces.lowerArc)
    (i : Fin B.faces.interface.count) (hi : i ≠ B.faces.lastCell)
    (hmono : T.IsMonochromatic (B.topSupportingLine i)) :
    CoordinateTriangleBoundaryIntersection C (B.faces.faceCoordinates (i, false))
      (meshTriangleBasis T t) (B.faces.faceBasis (i, false)) := by
  have hv : B.faces.vertex (i.succ, true) ∈
      C '' segment ℝ (B.chartTopVertex i.castSucc) (B.chartTopVertex i.succ) := by
    rw [B.chartTopSegment_image i, B.faces.top_vertex_eq_upper_endpoint i]
    exact mem_image_of_mem _ (by simp)
  obtain ⟨z, hz, hzv⟩ := hv
  have himage : C '' ({z} : Set Plane) = {B.faces.vertex (i.succ, true)} := by
    simp only [image_singleton, hzv]
  apply B.coreContact_of_convex_edge T t hsource (i, false) 0 {z}
    (singleton_subset_iff.mpr (B.chartTopSegment_subset_source i hz)) (convex_singleton z) ?_ ?_
    (B.topSupportingLine i) (B.topSupportingLine_spec i).1 hmono
    (singleton_subset_iff.mpr ((B.topSupportingLine_spec i).2 hz))
  · rw [himage]
    apply singleton_subset_iff.mpr
    rw [B.faces.top_vertex_eq_lower_endpoint i]
    exact mem_image_of_mem _ (by simp)
  · rw [himage]
    exact (inter_subset_inter_left _ (image_mono (meshTriangleBasis_subset_support T t))).trans
      (B.faces.lower_carrier_inter_subset_vertex hinterior hlower hi)

omit [T2Space M] in
private theorem chartCornerSide_image (j : Fin 3) :
    C '' segment ℝ (B.firstUpperChartBasis 0) (B.firstUpperChartBasis j) =
      linearGraphCoordinates C G.frame ''
        segment ℝ (B.faces.firstUpperCornerBasis 0) (B.faces.firstUpperCornerBasis j) := by
  let L := collarParameterEquiv.trans G.frame.symm
  have himage (p q : Plane) : L '' segment ℝ p q = segment ℝ (L p) (L q) :=
    image_segment ℝ L.toLinearMap.toAffineMap p q
  change C '' segment ℝ (L (B.faces.firstUpperCornerBasis 0))
    (L (B.faces.firstUpperCornerBasis j)) = _
  rw [← himage, image_image]
  rfl

omit [T2Space M] in
private theorem chartCornerSide_one_image :
    C '' segment ℝ (B.firstUpperChartBasis 0) (B.firstUpperChartBasis 1) =
      ((B.faces.pair B.faces.firstCell).upper.boundary 0).map '' Icc (0 : ℝ) 1 := by
  rw [B.chartCornerSide_image, B.faces.first_upper_edge_image_eq_corner_side]

omit [T2Space M] in
private theorem chartCornerSide_two_image :
    C '' segment ℝ (B.firstUpperChartBasis 0) (B.firstUpperChartBasis 2) =
      ((B.faces.pair B.faces.firstCell).upper.boundary 2).map '' Icc (0 : ℝ) 1 := by
  rw [B.chartCornerSide_image, ← B.faces.leftCut_eq_corner_side]
  exact B.faces.left_edge_image.symm

private theorem first_upper_contact_of_monochromatic (T : TriangleMesh) (t : T.Triangle)
    (hsource : T.toPlaneComplex.support ⊆ C.source)
    (hinterior : Disjoint (C '' T.toPlaneComplex.support) (interior B.faces.carrier))
    (hlower : Disjoint (C '' T.toPlaneComplex.support) B.faces.lowerArc)
    (hcorner : T.IsMonochromatic (cornerSeparator B.firstUpperChartBasis))
    (hside : ∀ j : Fin 3, j = 1 ∨ j = 2 → T.IsMonochromatic (B.firstUpperChartBasis.coord j)) :
    CoordinateTriangleBoundaryIntersection C (B.faces.faceCoordinates (B.faces.firstCell, true))
      (meshTriangleBasis T t) (B.faces.faceBasis (B.faces.firstCell, true)) := by
  let K := convexHull ℝ (range (meshTriangleBasis T t))
  have hKsupport : K ⊆ T.toPlaneComplex.support := meshTriangleBasis_subset_support T t
  have hhalf : (∀ z ∈ K, 0 ≤ cornerSeparator B.firstUpperChartBasis z) ∨
      (∀ z ∈ K, cornerSeparator B.firstUpperChartBasis z ≤ 0) := by
    have h := hcorner.triangleCarrier_halfspace T t
    change (∀ z ∈ convexHull ℝ (T.position '' (t.1 : Set T.Vertex)),
      0 ≤ cornerSeparator B.firstUpperChartBasis z) ∨
      (∀ z ∈ convexHull ℝ (T.position '' (t.1 : Set T.Vertex)),
        cornerSeparator B.firstUpperChartBasis z ≤ 0) at h
    simpa only [K, range_meshTriangleBasis] using h
  have hbound : (C '' K) ∩ (B.faces.pair B.faces.firstCell).upper.carrier ⊆
      C '' (K ∩ (segment ℝ (B.firstUpperChartBasis 0) (B.firstUpperChartBasis 1) ∪
        segment ℝ (B.firstUpperChartBasis 0) (B.firstUpperChartBasis 2))) := by
    rintro y ⟨⟨z, hz, rfl⟩, hp⟩
    have hback : z ∈ C.symm '' (B.faces.pair B.faces.firstCell).upper.carrier :=
      ⟨C z, hp, C.left_inv (hsource (hKsupport hz))⟩
    exact ⟨z, ⟨hz, B.core_first_upper_contact_subset_corner_sides T hinterior hlower
      ⟨hKsupport hz, hback⟩⟩, rfl⟩
  rcases inter_corner_eq_one_side B.firstUpperChartBasis hhalf with hfirst | hsecond
  · apply B.coreContact_of_convex_edge T t hsource (B.faces.firstCell, true) 0
      (segment ℝ (B.firstUpperChartBasis 0) (B.firstUpperChartBasis 1))
      (subset_union_left.trans B.firstUpperChartSides_subset_source) (convex_segment _ _)
      B.chartCornerSide_one_image.subset ?_ (B.firstUpperChartBasis.coord 2)
      (B.firstUpperChartBasis.surjective_coord 2) (hside 2 (Or.inr rfl)) ?_
    · rw [hfirst] at hbound
      exact hbound.trans (image_mono inter_subset_right)
    · rintro z hz
      rw [segment_eq_image_lineMap] at hz
      obtain ⟨s, -, rfl⟩ := hz
      simp [AffineMap.apply_lineMap]
  · apply B.coreContact_of_convex_edge T t hsource (B.faces.firstCell, true) 2
      (segment ℝ (B.firstUpperChartBasis 0) (B.firstUpperChartBasis 2))
      (subset_union_right.trans B.firstUpperChartSides_subset_source) (convex_segment _ _)
      B.chartCornerSide_two_image.subset ?_ (B.firstUpperChartBasis.coord 1)
      (B.firstUpperChartBasis.surjective_coord 1) (hside 1 (Or.inl rfl)) ?_
    · rw [hsecond] at hbound
      exact hbound.trans (image_mono inter_subset_right)
    · rintro z hz
      rw [segment_eq_image_lineMap] at hz
      obtain ⟨s, -, rfl⟩ := hz
      simp [AffineMap.apply_lineMap]

theorem core_boundaryIntersections_of_monochromatic (T : TriangleMesh)
    (hsource : T.toPlaneComplex.support ⊆ C.source)
    (hinterior : Disjoint (C '' T.toPlaneComplex.support) (interior B.faces.carrier))
    (hlower : Disjoint (C '' T.toPlaneComplex.support) B.faces.lowerArc)
    (hmono : ∀ l ∈ B.coreContactLines, T.IsMonochromatic l)
    (t : T.Triangle) (i : Fin B.faces.interface.count × Bool) :
    CoordinateTriangleBoundaryIntersection C (B.faces.faceCoordinates i)
      (meshTriangleBasis T t) (B.faces.faceBasis i) := by
  have htop (j : Fin B.faces.interface.count) : T.IsMonochromatic (B.topSupportingLine j) :=
    hmono _ (by simp [coreContactLines, List.mem_ofFn])
  rcases i with ⟨i, _ | _⟩
  · by_cases hi : i = B.faces.lastCell
    · subst i
      exact B.right_contact_of_monochromatic T t hsource hinterior hlower
        (hmono _ (by simp [coreContactLines]))
    · exact B.lower_contact_of_monochromatic T t hsource hinterior hlower i hi (htop i)
  · by_cases hi : i = B.faces.firstCell
    · subst i
      apply B.first_upper_contact_of_monochromatic T t hsource hinterior hlower
        (hmono _ (by simp [coreContactLines]))
      intro j hj
      rcases hj with rfl | rfl <;> exact hmono _ (by simp [coreContactLines])
    · exact B.upper_contact_of_monochromatic T t hsource hinterior hlower i hi (htop i)

end FiniteChartRegionDecomposition.OrientedGraphPiece.FixedStripBandFaces

namespace FiniteChartRegionDecomposition

theorem exists_simultaneous_core_band_refinement
    {D : FiniteChartRegionDecomposition (M := M)} {C : OpenPartialHomeomorph Plane M}
    {I : Type*} [Finite I] {e : I → D.EdgeIndex} {R : I → D.regions}
    {a b ua wa ub wb δ ra rb : I → ℝ}
    {G : ∀ i, D.OrientedGraphPiece (e i) (R i) C (a i) (b i)}
    {P : ∀ i, TransverseGraphCuts (G i).lower ((G i).parameter (a i)) ((G i).parameter (b i))
      (ua i) (wa i) (ub i) (wb i)}
    (B : ∀ i, (G i).FixedStripBandFaces (P i) (δ i) (ra i) (rb i))
    (T : TriangleMesh) (hsource : T.toPlaneComplex.support ⊆ C.source)
    (hinterior : ∀ i, Disjoint (C '' T.toPlaneComplex.support) (interior (B i).faces.carrier))
    (hlower : ∀ i, Disjoint (C '' T.toPlaneComplex.support) (B i).faces.lowerArc)
    (extra : List (Plane →ᵃ[ℝ] ℝ) := []) :
    ∃ T' : TriangleMesh,
      T'.toPlaneComplex.support = T.toPlaneComplex.support ∧
      T'.toPlaneComplex.Subdivides T.toPlaneComplex ∧
      (∀ i l, l ∈ (B i).coreContactLines → T'.IsMonochromatic l) ∧
      (∀ l ∈ extra, T'.IsMonochromatic l) ∧
      ∀ (i : I) (t : T'.Triangle) (j : Fin (B i).faces.interface.count × Bool),
        CoordinateTriangleBoundaryIntersection C ((B i).faces.faceCoordinates j)
          (meshTriangleBasis T' t) ((B i).faces.faceBasis j) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let lines := (Finset.univ : Finset I).toList.flatMap (fun i => (B i).coreContactLines) ++ extra
  let T' := T.refineByLines lines
  have hs : T'.toPlaneComplex.support = T.toPlaneComplex.support :=
    T.refineByLines_support lines
  have hmono (i : I) (l : Plane →ᵃ[ℝ] ℝ) (hl : l ∈ (B i).coreContactLines) :
      T'.IsMonochromatic l :=
    T.refineByLines_isMonochromatic_of_mem lines
      (List.mem_append_left _ (List.mem_flatMap.mpr ⟨i, by simp, hl⟩))
  refine ⟨T', hs, T.refineByLines_subdivides lines, hmono,
    fun l hl => T.refineByLines_isMonochromatic_of_mem lines (List.mem_append_right _ hl), ?_⟩
  intro i t j
  exact (B i).core_boundaryIntersections_of_monochromatic T'
    (by rwa [hs]) (by simpa only [hs] using hinterior i)
    (by simpa only [hs] using hlower i) (hmono i) t j

end FiniteChartRegionDecomposition
end PoincareConjecture.Topology.Surface
