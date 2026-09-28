


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Bands.Oblique








set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology Matrix
open Poincare.Topology.Plane.Curves Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

namespace SmoothGraphBandPair

variable {F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M}
  {lo hi : ℝ → ℝ} {a b : ℝ} {hab : a < b}
  (B : SmoothGraphBandPair F lo hi hab)
  {U : Set ℝ} (hU : IsOpen U)
  (hlo : ContDiffOn ℝ ∞ lo U) (hhi : ContDiffOn ℝ ∞ hi U)


noncomputable def faceCoordinates (_B : SmoothGraphBandPair F lo hi hab)
    (hU : IsOpen U) (hlo : ContDiffOn ℝ ∞ lo U) (hhi : ContDiffOn ℝ ∞ hi U) :
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M :=
  (((collarParameterEquiv.toHomeomorph.toOpenPartialHomeomorph.trans
    (graphStripCoordinates (hU.inter (isOpen_interior (s := {t | lo t < hi t})))
      (hlo.mono inter_subset_left) (hhi.mono inter_subset_left)
      (fun t ht => show t ∈ {t | lo t < hi t} from interior_subset ht.2))).trans
    collarParameterEquiv.symm.toHomeomorph.toOpenPartialHomeomorph).trans F)


noncomputable def faceBasis (_B : SmoothGraphBandPair F lo hi hab) :
    Bool → AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))
  | false => rectangleLowerBasis hab zero_lt_one
  | true => rectangleUpperBasis hab zero_lt_one

omit [T2Space M] in
theorem face_map_eq_coordinates (i : Bool) :
    (B.face i).map = B.faceCoordinates hU hlo hhi := by
  cases i
  · exact B.lower_map
  · exact B.upper_map.trans B.lower_map

omit [T2Space M] in
theorem face_source_eq_triangle (i : Bool) :
    (B.face i).source = convexHull ℝ (range (B.faceBasis i)) := by
  cases i
  · exact B.lower_source
  · exact B.upper_source

omit [T2Space M] in
theorem face_carrier_eq_coordinates (i : Bool) :
    (B.face i).carrier = B.faceCoordinates hU hlo hhi ''
      convexHull ℝ (range (B.faceBasis i)) := by
  rw [(B.face i).carrier_eq_image, B.face_map_eq_coordinates hU hlo hhi,
    B.face_source_eq_triangle]

omit [T2Space M] in
theorem smooth_faceCoordinates
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source) :
    ContMDiffOn (𝓡 2) (𝓡 2) ∞ (B.faceCoordinates hU hlo hhi)
      (B.faceCoordinates hU hlo hhi).source := by
  let L := collarParameterEquiv
  let G := graphStripCoordinates (hU.inter (isOpen_interior (s := {t | lo t < hi t})))
    (hlo.mono inter_subset_left) (hhi.mono inter_subset_left)
    (fun t ht => show t ∈ {t | lo t < hi t} from interior_subset ht.2)
  let H := (L.toHomeomorph.toOpenPartialHomeomorph.trans G).trans
    L.symm.toHomeomorph.toOpenPartialHomeomorph
  have hG : ContDiffOn ℝ ∞ G G.source :=
    contDiffOn_graphStripMap (hlo.mono inter_subset_left) (hhi.mono inter_subset_left)
  have hH : ContDiffOn ℝ ∞ H H.source :=
    L.symm.contDiff.comp_contDiffOn
      (hG.comp L.contDiff.contDiffOn (fun _ hz => hz.1.2))
  exact hF.comp (hH.contMDiffOn.mono (fun _ hz => hz.1)) (fun _ hz => hz.2)

omit [T2Space M] in
theorem smooth_faceCoordinates_symm
    (hFinv : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target) :
    ContMDiffOn (𝓡 2) (𝓡 2) ∞ (B.faceCoordinates hU hlo hhi).symm
      (B.faceCoordinates hU hlo hhi).target := by
  let L := collarParameterEquiv
  let G := graphStripCoordinates (hU.inter (isOpen_interior (s := {t | lo t < hi t})))
    (hlo.mono inter_subset_left) (hhi.mono inter_subset_left)
    (fun t ht => show t ∈ {t | lo t < hi t} from interior_subset ht.2)
  let H := (L.toHomeomorph.toOpenPartialHomeomorph.trans G).trans
    L.symm.toHomeomorph.toOpenPartialHomeomorph
  have hGinv : ContDiffOn ℝ ∞ G.symm G.target :=
    contDiffOn_graphStripInv (hlo.mono inter_subset_left) (hhi.mono inter_subset_left)
      (fun t ht => show t ∈ {t | lo t < hi t} from interior_subset ht.2)
  have hHinv : ContDiffOn ℝ ∞ H.symm H.target :=
    L.symm.contDiff.comp_contDiffOn
      (hGinv.comp L.contDiff.contDiffOn (fun _ hz => hz.2.1))
  exact hHinv.contMDiffOn.comp (hFinv.mono (fun _ hz => hz.1)) (fun _ hz => hz.2)

omit [T2Space M] in
theorem rectangle_subset_faceCoordinates_source (hI : Icc a b ⊆ U) :
    {z : EuclideanSpace ℝ (Fin 2) | z 0 ∈ Icc a b ∧ z 1 ∈ Icc (0 : ℝ) 1} ⊆
      (B.faceCoordinates hU hlo hhi).source := by
  intro z hz
  refine ⟨⟨⟨mem_univ _, ?_⟩, mem_univ _⟩, ?_⟩
  · refine ⟨⟨hI hz.1, mem_interior_iff_mem_nhds.mpr ?_⟩, mem_univ _⟩
    exact ((hlo _ (hI hz.1)).continuousWithinAt.continuousAt
      (hU.mem_nhds (hI hz.1))).eventually_lt
      ((hhi _ (hI hz.1)).continuousWithinAt.continuousAt
        (hU.mem_nhds (hI hz.1))) (B.gap _ hz.1)
  · apply B.band_subset_source
    change collarParameterEquiv
      (collarParameterEquiv.symm (graphStripMap lo hi (collarParameterEquiv z))) ∈
        {q : ℝ × ℝ | q.1 ∈ Icc a b ∧ lo q.1 ≤ q.2 ∧ q.2 ≤ hi q.1}
    rw [collarParameterEquiv.apply_symm_apply, ← graphStripMap_image_rectangle B.gap]
    exact ⟨collarParameterEquiv z, hz, rfl⟩

omit [T2Space M] in
theorem face_triangle_subset_source (hI : Icc a b ⊆ U) (i : Bool) :
    convexHull ℝ (range (B.faceBasis i)) ⊆ (B.faceCoordinates hU hlo hhi).source := by
  apply Subset.trans _ (B.rectangle_subset_faceCoordinates_source hU hlo hhi hI)
  rw [← rectangle_triangle_union hab zero_lt_one]
  cases i
  · exact subset_union_left
  · exact subset_union_right

omit [T2Space M] in
theorem face_coordinates_subset_chart (i : Bool) :
    B.faceCoordinates hU hlo hhi '' convexHull ℝ (range (B.faceBasis i)) ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) (B.face i).chart).source := by
  rw [← B.face_carrier_eq_coordinates hU hlo hhi]
  exact (B.face i).carrier_subset_chart

theorem face_frontier_eq_coordinates (hI : Icc a b ⊆ U) (i : Bool) :
    frontier (B.face i).carrier = B.faceCoordinates hU hlo hhi ''
      frontier (convexHull ℝ (range (B.faceBasis i))) := by
  let C := B.faceCoordinates hU hlo hhi
  let K := convexHull ℝ (range (B.faceBasis i))
  have hK : IsCompact K := (finite_range (B.faceBasis i)).isCompact_convexHull ℝ
  have hsub : K ⊆ C.source := B.face_triangle_subset_source hU hlo hhi hI i
  have himage : C '' K ⊆ C.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact C.map_source (hsub hz)
  have hcimage := hK.image_of_continuousOn (C.continuousOn.mono hsub)
  have hisimage : C.IsImage K (C '' K) := by
    intro z hz
    constructor
    · rintro ⟨w, hw, heq⟩
      exact C.injOn (hsub hw) hz heq ▸ hw
    · exact mem_image_of_mem C
  rw [B.face_carrier_eq_coordinates hU hlo hhi]
  simpa only [inter_eq_right.mpr (hK.isClosed.frontier_subset.trans hsub),
    inter_eq_right.mpr (hcimage.isClosed.frontier_subset.trans himage)] using
    hisimage.frontier.image_eq.symm

omit [T2Space M] in
private theorem diagonal_image (hI : Icc a b ⊆ U) :
    (B.lower.boundary 1).map '' Icc (0 : ℝ) 1 =
      (B.faceCoordinates hU hlo hhi ∘ affineChartSegment
        (!₂[a, 0] : EuclideanSpace ℝ (Fin 2)) !₂[b, 1]) '' Icc (0 : ℝ) 1 := by
  rw [← B.diagonal_inter]
  change (B.face false).carrier ∩ (B.face true).carrier = _
  rw [B.face_carrier_eq_coordinates hU hlo hhi,
    B.face_carrier_eq_coordinates hU hlo hhi,
    ← (B.faceCoordinates hU hlo hhi).injOn.image_inter
      (B.face_triangle_subset_source hU hlo hhi hI false)
      (B.face_triangle_subset_source hU hlo hhi hI true)]
  change B.faceCoordinates hU hlo hhi ''
    (convexHull ℝ (range (rectangleLowerBasis hab zero_lt_one)) ∩
      convexHull ℝ (range (rectangleUpperBasis hab zero_lt_one))) = _
  rw [rectangle_triangle_inter hab zero_lt_one]
  have hseg : affineChartSegment (!₂[a, 0] : EuclideanSpace ℝ (Fin 2)) !₂[b, 1] ''
      Icc (0 : ℝ) 1 = affineSegment ℝ (!₂[a, 0] : EuclideanSpace ℝ (Fin 2)) !₂[b, 1] := by
    unfold affineSegment
    congr 1
    funext t
    simp [affineChartSegment, AffineMap.lineMap_apply, add_comm]
  rw [← hseg, image_image]
  rfl

omit [T2Space M] in

theorem face_boundary_image (hI : Icc a b ⊆ U) (i : Bool) (k : Fin 3) :
    ((B.face i).boundary k).map '' Icc (0 : ℝ) 1 =
      (B.faceCoordinates hU hlo hhi ∘ affineChartSegment
        (B.faceBasis i (k.succAbove 0)) (B.faceBasis i (k.succAbove 1))) ''
          Icc (0 : ℝ) 1 := by
  cases i <;> fin_cases k
  · apply congrArg (fun f : ℝ → M => f '' Icc (0 : ℝ) 1)
    funext t
    change (B.lower.boundary 0).map t = _
    rw [B.right_edge]
    change F (collarParameterEquiv.symm (b, lo b + t * (hi b - lo b))) =
      F (collarParameterEquiv.symm (graphStripMap lo hi
        (collarParameterEquiv (affineChartSegment !₂[b, 0] !₂[b, 1] t))))
    have he : collarParameterEquiv
        (affineChartSegment (!₂[b, 0] : EuclideanSpace ℝ (Fin 2)) !₂[b, 1] t) = (b, t) := by
      ext <;> simp [affineChartSegment, collarParameterEquiv]
    rw [he]
    rfl
  · exact B.diagonal_image hU hlo hhi hI
  · apply congrArg (fun f : ℝ → M => f '' Icc (0 : ℝ) 1)
    funext t
    change (B.lower.boundary 2).map t = _
    rw [B.lower_edge]
    change F (collarParameterEquiv.symm (a + t * (b - a), lo (a + t * (b - a)))) =
      F (collarParameterEquiv.symm (graphStripMap lo hi
        (collarParameterEquiv (affineChartSegment !₂[a, 0] !₂[b, 0] t))))
    have he : collarParameterEquiv
        (affineChartSegment (!₂[a, 0] : EuclideanSpace ℝ (Fin 2)) !₂[b, 0] t) =
          (a + t * (b - a), 0) := by
      ext <;> simp [affineChartSegment, collarParameterEquiv]
    rw [he, graphStripMap_lower]
  · apply congrArg (fun f : ℝ → M => f '' Icc (0 : ℝ) 1)
    funext t
    change (B.upper.boundary 0).map t = _
    rw [B.upper_edge]
    change F (collarParameterEquiv.symm (a + t * (b - a), hi (a + t * (b - a)))) =
      F (collarParameterEquiv.symm (graphStripMap lo hi
        (collarParameterEquiv (affineChartSegment !₂[a, 1] !₂[b, 1] t))))
    have he : collarParameterEquiv
        (affineChartSegment (!₂[a, 1] : EuclideanSpace ℝ (Fin 2)) !₂[b, 1] t) =
          (a + t * (b - a), 1) := by
      ext <;> simp [affineChartSegment, collarParameterEquiv]
    rw [he, graphStripMap_upper]
  · change (B.upper.boundary 1).map '' Icc (0 : ℝ) 1 = _
    rw [← B.diagonal_eq]
    exact B.diagonal_image hU hlo hhi hI
  · apply congrArg (fun f : ℝ → M => f '' Icc (0 : ℝ) 1)
    funext t
    change (B.upper.boundary 2).map t = _
    rw [B.left_edge]
    change F (collarParameterEquiv.symm (a, lo a + t * (hi a - lo a))) =
      F (collarParameterEquiv.symm (graphStripMap lo hi
        (collarParameterEquiv (affineChartSegment !₂[a, 0] !₂[a, 1] t))))
    have he : collarParameterEquiv
        (affineChartSegment (!₂[a, 0] : EuclideanSpace ℝ (Fin 2)) !₂[a, 1] t) = (a, t) := by
      ext <;> simp [affineChartSegment, collarParameterEquiv]
    rw [he]
    rfl

end SmoothGraphBandPair

namespace ObliqueBandFaces

variable {F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M}
  {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
  (B : ObliqueBandFaces F lo a b ua wa ub wb ra rb)


noncomputable def faceCoordinates (i : Fin B.interface.count × Bool) :
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M :=
  (B.pair i.1).faceCoordinates
    (B.interface.pieceCoordinates B.open_domain B.smooth_lower i.1).parameter.open_target
    contDiffOn_const
    ((B.interface.pieceCoordinates B.open_domain B.smooth_lower i.1).smooth_upperGraph
      B.smooth_lower)


noncomputable def faceBasis (i : Fin B.interface.count × Bool) :
    AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)) := (B.pair i.1).faceBasis i.2

omit [T2Space M] in
theorem face_map_eq_coordinates (i : Fin B.interface.count × Bool) :
    (B.face i).map = B.faceCoordinates i :=
  (B.pair i.1).face_map_eq_coordinates _ _ _ i.2

omit [T2Space M] in
theorem face_source_eq_triangle (i : Fin B.interface.count × Bool) :
    (B.face i).source = convexHull ℝ (range (B.faceBasis i)) :=
  (B.pair i.1).face_source_eq_triangle i.2

omit [T2Space M] in
theorem face_carrier_eq_coordinates (i : Fin B.interface.count × Bool) :
    (B.face i).carrier = B.faceCoordinates i '' convexHull ℝ (range (B.faceBasis i)) :=
  (B.pair i.1).face_carrier_eq_coordinates _ _ _ i.2

omit [T2Space M] in
theorem smooth_faceCoordinates
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source) (i : Fin B.interface.count × Bool) :
    ContMDiffOn (𝓡 2) (𝓡 2) ∞ (B.faceCoordinates i) (B.faceCoordinates i).source :=
  (B.pair i.1).smooth_faceCoordinates _ _ _
    (smooth_obliqueSurfaceCoordinates F hF B.cuts B.open_domain B.smooth_lower)

omit [T2Space M] in
theorem smooth_faceCoordinates_symm
    (hFinv : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target) (i : Fin B.interface.count × Bool) :
    ContMDiffOn (𝓡 2) (𝓡 2) ∞ (B.faceCoordinates i).symm (B.faceCoordinates i).target :=
  (B.pair i.1).smooth_faceCoordinates_symm _ _ _
    (smooth_obliqueSurfaceCoordinates_symm F hFinv B.cuts B.open_domain B.smooth_lower)

omit [T2Space M] in
theorem face_triangle_subset_source (i : Fin B.interface.count × Bool) :
    convexHull ℝ (range (B.faceBasis i)) ⊆ (B.faceCoordinates i).source :=
  (B.pair i.1).face_triangle_subset_source _ _ _
    (fun _ ht => (B.interface.pieceCoordinates B.open_domain B.smooth_lower i.1).parameter_mem_target
      ht) i.2

omit [T2Space M] in
theorem face_coordinates_subset_chart (i : Fin B.interface.count × Bool) :
    B.faceCoordinates i '' convexHull ℝ (range (B.faceBasis i)) ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) (B.face i).chart).source :=
  (B.pair i.1).face_coordinates_subset_chart _ _ _ i.2

theorem face_frontier_eq_coordinates (i : Fin B.interface.count × Bool) :
    frontier (B.face i).carrier = B.faceCoordinates i ''
      frontier (convexHull ℝ (range (B.faceBasis i))) :=
  (B.pair i.1).face_frontier_eq_coordinates _ _ _
    (fun _ ht => (B.interface.pieceCoordinates B.open_domain B.smooth_lower i.1).parameter_mem_target
      ht) i.2

omit [T2Space M] in
theorem face_boundary_image (i : Fin B.interface.count × Bool) (k : Fin 3) :
    ((B.face i).boundary k).map '' Icc (0 : ℝ) 1 =
      (B.faceCoordinates i ∘ affineChartSegment
        (B.faceBasis i (k.succAbove 0)) (B.faceBasis i (k.succAbove 1))) '' Icc (0 : ℝ) 1 :=
  (B.pair i.1).face_boundary_image _ _ _
    (fun _ ht => (B.interface.pieceCoordinates B.open_domain B.smooth_lower i.1).parameter_mem_target
      ht) i.2 k

end ObliqueBandFaces

end PoincareConjecture.Topology.Surface
