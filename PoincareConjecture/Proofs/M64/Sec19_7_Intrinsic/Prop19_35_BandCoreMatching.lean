import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RetainedReturnCore
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Collars.CoreBandRefinement











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface Poincare.Topology.Plane.Meshes

namespace PoincareConjecture

private theorem core_triangle_contact
    (T : TriangleMesh) (t : T.Triangle) (face : SmoothFace AnnulusCoordinates)
    (C : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hsource : convexHull ℝ (range b) ⊆ C.source)
    (hcarrier : face.carrier = C '' convexHull ℝ (range b)) (k : Fin 3)
    (hboundary : (face.boundary k).map '' Icc (0 : ℝ) 1 =
      (C ∘ affineChartSegment (b (k.succAbove 0)) (b (k.succAbove 1))) '' Icc (0 : ℝ) 1)
    (p q : AnnulusCoordinates)
    (hedge : segment ℝ p q ⊆ (face.boundary k).map '' Icc (0 : ℝ) 1)
    (hcontact : convexHull ℝ (range (meshTriangleBasis T t)) ∩ face.carrier ⊆ segment ℝ p q)
    (l : AnnulusCoordinates →ᵃ[ℝ] ℝ) (hsurj : Function.Surjective l)
    (hmono : T.IsMonochromatic l) (hline : segment ℝ p q ⊆ {z | l z = 0}) :
    CoordinateTriangleBoundaryIntersection (OpenPartialHomeomorph.refl AnnulusCoordinates)
      C (meshTriangleBasis T t) b := by
  let A := convexHull ℝ (range (meshTriangleBasis T t))
  have hinside : segment ℝ p q ⊆ face.carrier := hedge.trans
    ((face.boundary_image_subset_frontier k).trans face.isClosed_carrier.frontier_subset)
  have heq : A ∩ face.carrier = A ∩ segment ℝ p q :=
    Subset.antisymm (fun _ hz => ⟨hz.1, hcontact hz⟩)
      (fun _ hz => ⟨hz.1, hinside hz.2⟩)
  have hside : (∀ j, 0 ≤ l (meshTriangleBasis T t j)) ∨
      (∀ j, l (meshTriangleBasis T t j) ≤ 0) := by
    have hv (j : Fin 3) : meshTriangleBasis T t j ∈ T.triangleCarrier t.1 := by
      change _ ∈ convexHull ℝ (T.position '' (t.1 : Set T.Vertex))
      rw [← range_meshTriangleBasis]
      exact subset_convexHull ℝ _ (mem_range_self _)
    rcases hmono.triangleCarrier_halfspace T t with hp | hn
    · exact Or.inl (fun j => hp _ (hv j))
    · exact Or.inr (fun j => hn _ (hv j))
  apply CoordinateTriangleBoundaryIntersection.of_convex_chart_contact
    (OpenPartialHomeomorph.refl AnnulusCoordinates) C (meshTriangleBasis T t) b
    (subset_univ _) hsource (segment ℝ p q) (convex_segment _ _) ?_ l hsurj
    hside hline k ?_
  · simpa only [OpenPartialHomeomorph.refl_apply, image_id, ← hcarrier] using heq
  · simp only [OpenPartialHomeomorph.refl_apply, image_id, ← hcarrier]
    apply (hcontact.trans hedge).trans
    rw [hboundary, image_comp]
    apply image_mono
    unfold affineSegment
    apply subset_of_eq
    congr 1
    funext s
    simp [affineChartSegment, AffineMap.lineMap_apply, add_comm]

open Classical in






theorem m64Intrinsic_linear_band_core_cut_lines
    (L : AnnulusCoordinates ≃L[ℝ] AnnulusCoordinates)
    {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
    (B : ObliqueBandFaces L.toHomeomorph.toOpenPartialHomeomorph
      lo a b ua wa ub wb ra rb)
    {U K R : Set AnnulusCoordinates} (hremove : B.carrier ⊆ R)
    (hlower : B.lowerArc ⊆ K)
    (hcover : ∀ p ∈ closure U ∩ K, ∃ W : Set AnnulusCoordinates,
      IsOpen W ∧ p ∈ W ∧ W ∩ closure U ⊆ R) :
    ∃ lines : List (Plane →ᵃ[ℝ] ℝ),
      (∀ l ∈ lines, Function.Surjective l) ∧
      ∀ T : TriangleMesh, T.toPlaneComplex.support ⊆ closure (U \ R) →
        (∀ l ∈ lines, T.IsMonochromatic l) →
        ∀ (t : T.Triangle) (i : Fin B.interface.count × Bool),
        CoordinateTriangleBoundaryIntersection (OpenPartialHomeomorph.refl AnnulusCoordinates)
          (B.faceCoordinates i) (meshTriangleBasis T t) (B.faceBasis i) := by
  have hdisj : Disjoint (closure (U \ R)) (interior B.carrier) := by
    apply disjoint_left.mpr
    intro z hz hi
    have hf := Poincare.Topology.closure_diff_inter_subset_frontier hremove
      ⟨hz, interior_subset hi⟩
    exact hf.2 hi
  have hlow : Disjoint (closure (U \ R)) B.lowerArc := by
    exact (Poincare.Topology.closure_diff_disjoint_of_local_cover hcover).mono_right hlower
  let J := collarParameterEquiv.symm.trans L
  have himage (p q : ℝ × ℝ) :
      (fun z => L (collarParameterEquiv.symm z)) '' segment ℝ p q =
        segment ℝ (J p) (J q) := image_segment ℝ J.toLinearMap.toAffineMap p q
  have htop (i : Fin B.interface.count) : ∃ p q : AnnulusCoordinates,
      ((B.pair i).upper.boundary 0).map '' Icc (0 : ℝ) 1 = segment ℝ p q := by
    rw [B.upper_edge_image]
    change ∃ p q, (fun z => L (collarParameterEquiv.symm z)) ''
      segment ℝ (B.interface.cut i.castSucc,
        lo (B.interface.cut i.castSucc) + B.interface.height i.castSucc)
        (B.interface.cut i.succ,
          lo (B.interface.cut i.succ) + B.interface.height i.succ) = segment ℝ p q
    rw [himage]
    exact ⟨_, _, rfl⟩
  have hright : ∃ p q : AnnulusCoordinates, B.rightCut = segment ℝ p q := by
    change ∃ p q, (fun z => L (collarParameterEquiv.symm z)) ''
      segment ℝ (b, lo b) (b + rb * ub, lo b + rb * wb) = segment ℝ p q
    rw [himage]
    exact ⟨_, _, rfl⟩
  let I := {i : Fin B.interface.count × Bool // i ≠ (B.firstCell, true)}
  have hdata (j : I) : ∃ (p q : AnnulusCoordinates) (k : Fin 3),
      segment ℝ p q ⊆ ((B.face j).boundary k).map '' Icc (0 : ℝ) 1 ∧
      closure (U \ R) ∩ (B.face j).carrier ⊆ segment ℝ p q := by
    rcases j with ⟨⟨i, _ | _⟩, hi⟩
    · by_cases hilast : i = B.lastCell
      · subst i
        obtain ⟨p, q, heq⟩ := hright
        refine ⟨p, q, 0, ?_, ?_⟩
        · rw [← heq]
          exact B.right_edge_image.symm.subset
        · rw [← heq]
          exact B.last_lower_carrier_inter_subset_rightCut hdisj hlow
      · refine ⟨B.vertex (i.succ, true), B.vertex (i.succ, true), 0, ?_, ?_⟩
        · rw [segment_same]
          apply singleton_subset_iff.mpr
          refine ⟨1, by simp, ?_⟩
          exact (B.top_vertex_eq_lower_endpoint i).symm
        · rw [segment_same]
          exact B.lower_carrier_inter_subset_vertex hdisj hlow hilast
    · obtain ⟨p, q, heq⟩ := htop i
      refine ⟨p, q, 0, heq.symm.subset, ?_⟩
      rw [← heq]
      exact B.upper_carrier_inter_subset_upper_edge hdisj hlow
        (fun he => hi (congrArg (fun i => (i, true)) he))
  choose p q k hedge hcontact using hdata
  choose line hsurj hline using fun i : I =>
    Poincare.Topology.Plane.exists_affine_line_containing_segment (p i) (q i)
  let corner : AffineBasis (Fin 3) ℝ Plane := affineBasisOfTriangle
    (fun j => L (B.firstUpperCornerBasis j))
    (B.firstUpperCornerBasis.ind.map' L.toLinearMap.toAffineMap L.injective)
  have hlinear (p q : Plane) : L '' segment ℝ p q = segment ℝ (L p) (L q) :=
    image_segment ℝ L.toLinearMap.toAffineMap p q
  have hcornerone : segment ℝ (corner 0) (corner 1) =
      ((B.pair B.firstCell).upper.boundary 0).map '' Icc (0 : ℝ) 1 := by
    rw [B.first_upper_edge_image_eq_corner_side]
    exact (hlinear _ _).symm
  have hcornertwo : segment ℝ (corner 0) (corner 2) =
      ((B.pair B.firstCell).upper.boundary 2).map '' Icc (0 : ℝ) 1 := by
    rw [B.left_edge_image]
    change segment ℝ (corner 0) (corner 2) = B.leftCut
    rw [B.leftCut_eq_corner_side]
    exact (hlinear _ _).symm
  have hcornercontact : closure (U \ R) ∩ (B.pair B.firstCell).upper.carrier ⊆
      segment ℝ (corner 0) (corner 1) ∪ segment ℝ (corner 0) (corner 2) := by
    have h := B.first_upper_carrier_inter_subset_corner_sides hdisj hlow
    rw [image_union] at h
    change closure (U \ R) ∩ (B.pair B.firstCell).upper.carrier ⊆
      L '' segment ℝ (B.firstUpperCornerBasis 0) (B.firstUpperCornerBasis 1) ∪
        L '' segment ℝ (B.firstUpperCornerBasis 0) (B.firstUpperCornerBasis 2) at h
    rw [hlinear, hlinear] at h
    exact h
  have hcornersub : segment ℝ (corner 0) (corner 1) ∪ segment ℝ (corner 0) (corner 2) ⊆
      (B.pair B.firstCell).upper.carrier := by
    rw [hcornerone, hcornertwo]
    exact union_subset
      (((B.pair B.firstCell).upper.boundary_image_subset_frontier 0).trans
        (B.pair B.firstCell).upper.isClosed_carrier.frontier_subset)
      (((B.pair B.firstCell).upper.boundary_image_subset_frontier 2).trans
        (B.pair B.firstCell).upper.isClosed_carrier.frontier_subset)
  let lines := [cornerSeparator corner, corner.coord 1, corner.coord 2] ++
    (Finset.univ : Finset I).toList.map line
  refine ⟨lines, ?_, ?_⟩
  · intro l hl
    simp only [lines, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with (rfl | rfl | rfl) | hl
    · exact cornerSeparator_surjective corner
    · exact corner.surjective_coord 1
    · exact corner.surjective_coord 2
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hl
      exact hsurj i
  intro S hs hlines t i
  have hmono (i : I) : S.IsMonochromatic (line i) := hlines _ (by simp [lines])
  have hsep : S.IsMonochromatic (cornerSeparator corner) := hlines _ (by simp [lines])
  have hside (j : Fin 3) (hj : j = 1 ∨ j = 2) : S.IsMonochromatic (corner.coord j) := by
    rcases hj with rfl | rfl <;> exact hlines _ (by simp [lines])
  have hA : convexHull ℝ (range (meshTriangleBasis S t)) ⊆ closure (U \ R) :=
    (meshTriangleBasis_subset_support S t).trans hs
  by_cases hi : i = (B.firstCell, true)
  · subst i
    let A := convexHull ℝ (range (meshTriangleBasis S t))
    have hhalf : (∀ z ∈ A, 0 ≤ cornerSeparator corner z) ∨
        (∀ z ∈ A, cornerSeparator corner z ≤ 0) := by
      have h := hsep.triangleCarrier_halfspace S t
      change (∀ z ∈ convexHull ℝ (S.position '' (t.1 : Set S.Vertex)), _) ∨
        (∀ z ∈ convexHull ℝ (S.position '' (t.1 : Set S.Vertex)), _) at h
      simpa only [A, range_meshTriangleBasis] using h
    have heq : A ∩ (B.pair B.firstCell).upper.carrier =
        A ∩ (segment ℝ (corner 0) (corner 1) ∪ segment ℝ (corner 0) (corner 2)) :=
      Subset.antisymm (fun _ hz => ⟨hz.1, hcornercontact ⟨hA hz.1, hz.2⟩⟩)
        (fun _ hz => ⟨hz.1, hcornersub hz.2⟩)
    rcases inter_corner_eq_one_side corner hhalf with hfirst | hsecond
    · apply core_triangle_contact S t (B.face (B.firstCell, true)) _ _
        (B.face_triangle_subset_source _) (B.face_carrier_eq_coordinates _) 0
        (B.face_boundary_image _ _) (corner 0) (corner 1) hcornerone.subset ?_
        (corner.coord 2) (corner.surjective_coord 2) (hside 2 (Or.inr rfl)) ?_
      · change A ∩ (B.pair B.firstCell).upper.carrier ⊆ _
        rw [heq, hfirst]
        exact inter_subset_right
      · rintro z hz
        rw [segment_eq_image_lineMap] at hz
        obtain ⟨s, _, rfl⟩ := hz
        simp [AffineMap.apply_lineMap]
    · apply core_triangle_contact S t (B.face (B.firstCell, true)) _ _
        (B.face_triangle_subset_source _) (B.face_carrier_eq_coordinates _) 2
        (B.face_boundary_image _ _) (corner 0) (corner 2) hcornertwo.subset ?_
        (corner.coord 1) (corner.surjective_coord 1) (hside 1 (Or.inl rfl)) ?_
      · change A ∩ (B.pair B.firstCell).upper.carrier ⊆ _
        rw [heq, hsecond]
        exact inter_subset_right
      · rintro z hz
        rw [segment_eq_image_lineMap] at hz
        obtain ⟨s, _, rfl⟩ := hz
        simp [AffineMap.apply_lineMap]
  · let j : I := ⟨i, hi⟩
    exact core_triangle_contact S t (B.face i) _ _ (B.face_triangle_subset_source i)
      (B.face_carrier_eq_coordinates i) (k j) (B.face_boundary_image i (k j))
      (p j) (q j) (hedge j) (fun _ hz => hcontact j ⟨hA hz.1, hz.2⟩)
      (line j) (hsurj j) (hmono j) (hline j)

open Classical in





theorem m64Intrinsic_refine_core_to_linear_band
    (L : AnnulusCoordinates ≃L[ℝ] AnnulusCoordinates)
    {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
    (B : ObliqueBandFaces L.toHomeomorph.toOpenPartialHomeomorph
      lo a b ua wa ub wb ra rb)
    {U K R : Set AnnulusCoordinates} (hremove : B.carrier ⊆ R)
    (hlower : B.lowerArc ⊆ K)
    (hcover : ∀ p ∈ closure U ∩ K, ∃ W : Set AnnulusCoordinates,
      IsOpen W ∧ p ∈ W ∧ W ∩ closure U ⊆ R)
    (T : TriangleMesh) (hT : T.toPlaneComplex.support = closure (U \ R)) :
    ∃ lines : List (Plane →ᵃ[ℝ] ℝ),
      (∀ l ∈ lines, Function.Surjective l) ∧
      (T.refineByLines lines).toPlaneComplex.support = T.toPlaneComplex.support ∧
      ∀ (t : (T.refineByLines lines).Triangle) (i : Fin B.interface.count × Bool),
        CoordinateTriangleBoundaryIntersection (OpenPartialHomeomorph.refl AnnulusCoordinates)
          (B.faceCoordinates i) (meshTriangleBasis (T.refineByLines lines) t) (B.faceBasis i) := by
  obtain ⟨lines, hsurj, hcontact⟩ := m64Intrinsic_linear_band_core_cut_lines
    L B hremove hlower hcover
  refine ⟨lines, hsurj, T.refineByLines_support lines, hcontact _ ?_ ?_⟩
  · rw [T.refineByLines_support, hT]
  · intro l hl
    exact T.refineByLines_isMonochromatic_of_mem lines hl

open Classical in






theorem m64Intrinsic_refine_core_to_linear_bands
    {I : Type*} [Finite I]
    (L : I → AnnulusCoordinates ≃L[ℝ] AnnulusCoordinates)
    (lo : I → ℝ → ℝ) (a b ua wa ub wb ra rb : I → ℝ)
    (B : ∀ i, ObliqueBandFaces (L i).toHomeomorph.toOpenPartialHomeomorph
      (lo i) (a i) (b i) (ua i) (wa i) (ub i) (wb i) (ra i) (rb i))
    {U K R : Set AnnulusCoordinates} (hremove : ∀ i, (B i).carrier ⊆ R)
    (hlower : ∀ i, (B i).lowerArc ⊆ K)
    (hcover : ∀ p ∈ closure U ∩ K, ∃ W : Set AnnulusCoordinates,
      IsOpen W ∧ p ∈ W ∧ W ∩ closure U ⊆ R)
    (T : TriangleMesh) (hT : T.toPlaneComplex.support = closure (U \ R)) :
    ∃ lines : List (Plane →ᵃ[ℝ] ℝ),
      (∀ l ∈ lines, Function.Surjective l) ∧
      (T.refineByLines lines).toPlaneComplex.support = T.toPlaneComplex.support ∧
      ∀ i (t : (T.refineByLines lines).Triangle) (j : Fin (B i).interface.count × Bool),
        CoordinateTriangleBoundaryIntersection (OpenPartialHomeomorph.refl AnnulusCoordinates)
          ((B i).faceCoordinates j) (meshTriangleBasis (T.refineByLines lines) t)
            ((B i).faceBasis j) := by
  let _ := Fintype.ofFinite I
  choose cuts hsurj hcontact using fun i => m64Intrinsic_linear_band_core_cut_lines
    (L i) (B i) (hremove i) (hlower i) hcover
  let lines := (Finset.univ : Finset I).toList.flatMap cuts
  have hmem (i : I) {l : Plane →ᵃ[ℝ] ℝ} (hl : l ∈ cuts i) : l ∈ lines :=
    List.mem_flatMap.mpr ⟨i, by simp, hl⟩
  refine ⟨lines, ?_, T.refineByLines_support lines, ?_⟩
  · intro l hl
    obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hl
    exact hsurj i l hi
  intro i
  apply hcontact i
  · rw [T.refineByLines_support, hT]
  · intro l hl
    exact T.refineByLines_isMonochromatic_of_mem lines (hmem i hl)

end PoincareConjecture
