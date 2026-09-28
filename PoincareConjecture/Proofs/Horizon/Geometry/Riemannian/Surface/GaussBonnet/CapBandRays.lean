import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.EndpointRays
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.CapOuterCorners
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.Boundary
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Collars.CapBandIntersections








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology
open Poincare.Topology.Plane.Triangles Poincare.Topology.Plane.Curves

namespace PoincareConjecture.Topology.Surface

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]

omit [IsManifold (𝓡 2) ∞ S] in


theorem coordinateTriangleVelocity_pos_smul_of_image_subset
    (F G : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b c : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hG : ContMDiffOn (𝓡 2) (𝓡 2) ∞ G G.source)
    (hGi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ G.symm G.target)
    (hb : convexHull ℝ (range b) ⊆ F.source)
    (hc : convexHull ℝ (range c) ⊆ G.source)
    {i j k l : Fin 3} (hij : i ≠ j) (hkl : k ≠ l)
    (himage : (fun t : ℝ => G (AffineMap.lineMap (c k) (c l) t)) '' Icc (0 : ℝ) 1 ⊆
      (fun t : ℝ => F (AffineMap.lineMap (b i) (b j) t)) '' Icc (0 : ℝ) 1)
    (hpoint : F (b i) = G (c k)) :
    ∃ a : ℝ, 0 < a ∧
      coordinateTriangleVelocity G c k l = a • coordinateTriangleVelocity F b i j := by
  let γ := fun t : ℝ => F (AffineMap.lineMap (b i) (b j) t)
  let η := fun t : ℝ => G (AffineMap.lineMap (c k) (c l) t)
  let e := coordinateTriangleChart F b
  let p := standardTriangleVertex i
  let v := standardTriangleVertex j - standardTriangleVertex i
  have hmap (t : ℝ) : e.symm (p + t • v) = γ t := by
    simpa only [e, p, v, γ, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm]
      using coordinateTriangleChart_side F b i j t
  have hv : v ≠ 0 := by
    intro hz
    have h := congrArg (triangleParameterEquiv b) (sub_eq_zero.mp hz)
    rw [triangleParameterEquiv_vertex, triangleParameterEquiv_vertex] at h
    exact hij (b.ind.injective h).symm
  have htarget (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : p + t • v ∈ e.target := by
    change p + t • v ∈ ((triangleParameterEquiv b).toHomeomorph.toOpenPartialHomeomorph.trans F).source
    refine ⟨mem_univ _, hb ?_⟩
    change triangleParameterEquiv b (p + t • v) ∈ convexHull ℝ (range b)
    have heq : p + t • v = AffineMap.lineMap (standardTriangleVertex i) (standardTriangleVertex j) t := by
      simp [p, v, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm]
    rw [heq, triangleParameterEquiv_side]
    exact (convex_convexHull ℝ (range b)).lineMap_mem
      (subset_convexHull ℝ _ (mem_range_self i)) (subset_convexHull ℝ _ (mem_range_self j)) ht
  have hη (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 2) ∞ η t :=
    (coordinateTriangle_side_velocity G c hG hGi hc k l ht).1
  obtain ⟨φ, hφ, hmaps, heq, huniq⟩ := LeviCivitaData.exists_smooth_chart_edge_parameter
    e (coordinateTriangleChart_smooth F b hFi) p v hv htarget hη
    (show MapsTo η (Icc (0 : ℝ) 1) ((fun t : ℝ => e.symm (p + t • v)) '' Icc (0 : ℝ) 1) from by
      simpa only [hmap] using (show MapsTo η (Icc (0 : ℝ) 1) (γ '' Icc (0 : ℝ) 1) from
        fun t ht => himage (mem_image_of_mem η ht)))
  have heq' : EqOn η (γ ∘ φ) (Icc (0 : ℝ) 1) := by
    intro t ht
    simpa only [Function.comp_apply, hmap] using heq t ht
  have hzero : φ 0 = 0 := by
    apply huniq 0 (by simp) 0 (by simp)
    rw [hmap]
    simpa only [η, γ, AffineMap.lineMap_apply_zero] using hpoint.symm
  have hηinj : InjOn η (Icc (0 : ℝ) 1) := by
    intro s hs t ht he
    apply AffineMap.lineMap_injective ℝ (c.ind.injective.ne hkl)
    apply G.injOn
      (hc ((convex_convexHull ℝ (range c)).lineMap_mem
        (subset_convexHull ℝ _ (mem_range_self k)) (subset_convexHull ℝ _ (mem_range_self l)) hs))
      (hc ((convex_convexHull ℝ (range c)).lineMap_mem
        (subset_convexHull ℝ _ (mem_range_self k)) (subset_convexHull ℝ _ (mem_range_self l)) ht)) he
  have hφinj : InjOn φ (Icc (0 : ℝ) 1) := by
    intro s hs t ht he
    apply hηinj hs ht
    rw [heq' hs, heq' ht, Function.comp_apply, Function.comp_apply, he]
  have hcont : ContinuousOn φ (Icc (0 : ℝ) 1) :=
    fun t ht => (hφ t ht).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn φ (Icc (0 : ℝ) 1) := by
    rcases hcont.strictMonoOn_of_injOn_Icc' zero_le_one hφinj with hm | hm
    · exact hm
    · have hn := hm (by simp : (0 : ℝ) ∈ Icc 0 1) (by simp : (1 : ℝ) ∈ Icc 0 1) zero_lt_one
      have hp := (hmaps (by simp : (1 : ℝ) ∈ Icc 0 1)).1
      rw [hzero] at hn
      exact (not_lt_of_ge hp hn).elim
  have hdiff : DifferentiableAt ℝ φ 0 := (hφ 0 (by simp)).differentiableAt (by simp)
  have hnonneg : 0 ≤ deriv φ 0 := by
    have h := hmono.monotoneOn.derivWithin_nonneg (x := 0)
    rwa [hdiff.derivWithin (uniqueDiffOn_Icc zero_lt_one 0 (by simp))] at h
  have hvelocity : coordinateTriangleVelocity G c k l =
      deriv φ 0 • coordinateTriangleVelocity F b i j :=
    mfderiv_curve_reparam_zero_of_eqOn
      ((coordinateTriangle_side_velocity F b hF hFi hb i j (by simp : (0 : ℝ) ∈ Icc 0 1)).1.mdifferentiableAt (by simp))
      ((hη 0 (by simp)).mdifferentiableAt (by simp)) hdiff hzero heq'
  have hne : deriv φ 0 ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at hvelocity
    exact coordinateTriangleVelocity_ne_zero G c hG hGi hc hkl hvelocity
  exact ⟨deriv φ 0, lt_of_le_of_ne hnonneg hne.symm, hvelocity⟩

namespace FiniteChartRegionDecomposition.CapGraphEndpoint

variable {D : FiniteChartRegionDecomposition (M := S)}
  {P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : S)}
  {region : D.vertices → Bool × Bool → D.regions} {chart : D.regions → S}
  {caps : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p)
    (fun s => chart (region p s))}
  {e : D.EdgeIndex} {R : D.regions} {a b trim : ℝ} {terminal : Bool}
  {G : D.OrientedGraphPiece e R (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).symm a b}
  (E : D.CapGraphEndpoint P region chart caps e R G terminal trim)


def chordStartIndex : Fin 3 := if E.radialEdge = 1 then 2 else 1


def chordEndIndex : Fin 3 := if E.radialEdge = 1 then 1 else 2

theorem chord_indices_ne : E.chordStartIndex ≠ E.chordEndIndex := by
  unfold chordStartIndex chordEndIndex
  split_ifs <;> decide


theorem chord_start_eq_tip :
    (caps (D.edgeEndpoint e terminal)).coordinates E.sector
      (rightTriangleBasis (caps (D.edgeEndpoint e terminal)).scale_pos E.chordStartIndex) =
        D.edgeFromEndpoint e terminal trim := by
  have h := E.radial_end
  rw [(caps _).boundary_map] at h
  rcases E.radialEdge_valid with he | he
  · simpa [chordStartIndex, he, affineChartSegment] using h
  · simpa [chordStartIndex, he, affineChartSegment, Fin.succAbove, Fin.lt_def] using h



theorem chord_ray_map (t : ℝ) :
    (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).symm
      (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R) (D.edgeFromEndpoint e terminal trim) +
        t • E.direction) =
    (caps (D.edgeEndpoint e terminal)).coordinates E.sector
      (AffineMap.lineMap
        (rightTriangleBasis (caps (D.edgeEndpoint e terminal)).scale_pos E.chordStartIndex)
        (rightTriangleBasis (caps (D.edgeEndpoint e terminal)).scale_pos E.chordEndIndex) t) := by
  rw [E.chord_map, (caps _).boundary_map]
  change (caps _).coordinates E.sector (affineChartSegment _ _ _) = _
  by_cases he : E.radialEdge = 1
  · simp only [if_pos he, chordStartIndex, chordEndIndex]
    rw [← AffineMap.lineMap_apply_one_sub]
    congr 1
    simp [affineChartSegment, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm,
      Fin.succAbove]
  · simp only [if_neg he, chordStartIndex, chordEndIndex]
    congr 1
    simp [affineChartSegment, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm,
      Fin.succAbove]



theorem chordSegment_subset_coordinate_side {r : ℝ} (hr : r ≤ 1) :
    E.chordSegment r ⊆
      (fun t : ℝ => (caps (D.edgeEndpoint e terminal)).coordinates E.sector
        (AffineMap.lineMap
          (rightTriangleBasis (caps (D.edgeEndpoint e terminal)).scale_pos E.chordStartIndex)
          (rightTriangleBasis (caps (D.edgeEndpoint e terminal)).scale_pos E.chordEndIndex) t)) ''
        Icc (0 : ℝ) 1 := by
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨t, ⟨ht.1, ht.2.trans hr⟩, (E.chord_ray_map t).symm⟩


noncomputable def chordVelocity : TangentSpace (𝓡 2) (D.edgeFromEndpoint e terminal trim) :=
  coordinateTriangleVelocity ((caps (D.edgeEndpoint e terminal)).coordinates E.sector)
    (rightTriangleBasis (caps (D.edgeEndpoint e terminal)).scale_pos)
    E.chordStartIndex E.chordEndIndex

theorem chordVelocity_eq_firstOuterChord (he : E.radialEdge = 2) :
    E.chordVelocity = (caps (D.edgeEndpoint e terminal)).firstOuterChord E.sector.1 E.sector.2 := by
  dsimp only [TangentSpace]
  simp only [chordVelocity, chordStartIndex, chordEndIndex, he,
    show (2 : Fin 3) ≠ 1 by decide, if_false, Prod.eta,
    ChartCircleArrangementVertexPatch.VertexCapFaces.firstOuterChord]
  exact congrArg (fun k : Fin 3 =>
    (coordinateTriangleVelocity ((caps (D.edgeEndpoint e terminal)).coordinates E.sector)
      (rightTriangleBasis (caps (D.edgeEndpoint e terminal)).scale_pos) k 2 :
        EuclideanSpace ℝ (Fin 2))) (by simp [he])

theorem chordVelocity_eq_secondOuterChord (he : E.radialEdge = 1) :
    E.chordVelocity = (caps (D.edgeEndpoint e terminal)).secondOuterChord E.sector.2 E.sector.1 := by
  dsimp only [TangentSpace]
  simp only [chordVelocity, chordStartIndex, chordEndIndex, he, if_true, Prod.eta,
    ChartCircleArrangementVertexPatch.VertexCapFaces.secondOuterChord]
  exact congrArg (fun k : Fin 3 =>
    (coordinateTriangleVelocity ((caps (D.edgeEndpoint e terminal)).coordinates E.sector)
      (rightTriangleBasis (caps (D.edgeEndpoint e terminal)).scale_pos) k 1 :
        EuclideanSpace ℝ (Fin 2))) (by simp [he])

theorem tip_eq_firstOuterTip (he : E.radialEdge = 2) :
    D.edgeFromEndpoint e terminal trim =
      (caps (D.edgeEndpoint e terminal)).firstOuterTip E.sector.1 := by
  rw [← E.chord_start_eq_tip]
  simp only [chordStartIndex, he, show (2 : Fin 3) ≠ 1 by decide, if_false]
  exact (caps _).coordinate_first_outer_tip E.sector.1 E.sector.2

theorem tip_eq_secondOuterTip (he : E.radialEdge = 1) :
    D.edgeFromEndpoint e terminal trim =
      (caps (D.edgeEndpoint e terminal)).secondOuterTip E.sector.2 := by
  rw [← E.chord_start_eq_tip]
  simp only [chordStartIndex, he, if_true]
  exact (caps _).coordinate_second_outer_tip E.sector.2 E.sector.1

end FiniteChartRegionDecomposition.CapGraphEndpoint

namespace ObliqueBandFaces

variable {F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S}
  {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
  (B : ObliqueBandFaces F lo a b ua wa ub wb ra rb)



theorem left_endpoint_coordinate_map (t : ℝ) :
    B.faceCoordinates (B.firstCell, true)
      (AffineMap.lineMap (B.faceBasis (B.firstCell, true) 0)
        (B.faceBasis (B.firstCell, true) 1) t) = (B.endpointEdge false).map t := by
  have h := (B.pair B.firstCell).left_chart_map
    (B.interface.pieceCoordinates B.open_domain B.smooth_lower B.firstCell).parameter.open_target
    contDiffOn_const
    ((B.interface.pieceCoordinates B.open_domain B.smooth_lower B.firstCell).smooth_upperGraph
      B.smooth_lower) t
  rw [coordinateTriangle_first_map] at h
  exact h



theorem right_endpoint_coordinate_map (t : ℝ) :
    B.faceCoordinates (B.lastCell, false)
      (AffineMap.lineMap (B.faceBasis (B.lastCell, false) 1)
        (B.faceBasis (B.lastCell, false) 2) t) = (B.endpointEdge true).map t := by
  have h := (B.pair B.lastCell).right_chart_map
    (B.interface.pieceCoordinates B.open_domain B.smooth_lower B.lastCell).parameter.open_target
    contDiffOn_const
    ((B.interface.pieceCoordinates B.open_domain B.smooth_lower B.lastCell).smooth_upperGraph
      B.smooth_lower) t
  rw [coordinateTriangle_chord_map] at h
  exact h

end ObliqueBandFaces

namespace FiniteChartRegionDecomposition.OrientedGraphPiece.FixedStripBandFaces

variable {D : FiniteChartRegionDecomposition (M := S)} {e : D.EdgeIndex} {R : D.regions}
  {C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S} {a b : ℝ}
  {G : D.OrientedGraphPiece e R C a b} {ua wa ub wb : ℝ}
  {P : TransverseGraphCuts G.lower (G.parameter a) (G.parameter b) ua wa ub wb}
  {δ ra rb : ℝ} (B : G.FixedStripBandFaces P δ ra rb)



theorem left_endpoint_coordinate_start (hab : a ≤ b) :
    B.faces.faceCoordinates (B.faces.firstCell, true)
      (B.faces.faceBasis (B.faces.firstCell, true) 0) = (D.edge e.1 e.2).map a := by
  have h := B.faces.left_endpoint_coordinate_map 0
  simp only [AffineMap.lineMap_apply_zero] at h
  rw [h, B.faces.endpointEdge_map]
  change B.faces.coordinates (collarParameterEquiv.symm (0, 0 * B.faces.height 0)) = _
  rw [zero_mul, B.coordinates_eq, G.strip_axis]
  simp only [zero_mul, add_zero]
  exact (G.graph_map a (G.interval_source (left_mem_Icc.mpr hab))).symm



theorem right_endpoint_coordinate_start (hab : a ≤ b) :
    B.faces.faceCoordinates (B.faces.lastCell, false)
      (B.faces.faceBasis (B.faces.lastCell, false) 1) = (D.edge e.1 e.2).map b := by
  have h := B.faces.right_endpoint_coordinate_map 0
  simp only [AffineMap.lineMap_apply_zero] at h
  rw [h, B.faces.endpointEdge_map]
  change B.faces.coordinates (collarParameterEquiv.symm (1, 0 * B.faces.height 1)) = _
  rw [zero_mul, B.coordinates_eq, G.strip_axis]
  simp only [one_mul, add_sub_cancel]
  exact (G.graph_map b (G.interval_source (right_mem_Icc.mpr hab))).symm

end FiniteChartRegionDecomposition.OrientedGraphPiece.FixedStripBandFaces

namespace FiniteChartRegionDecomposition.OrientedEdgeGraphSubdivision.CutChain

variable {D : FiniteChartRegionDecomposition (M := S)}
  {P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : S)}
  {region : D.vertices → Bool × Bool → D.regions} {chart : D.regions → S}
  {caps : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p)
    (fun s => chart (region p s))}
  {cut : D.EdgeIndex → Bool → ℝ} {e : D.EdgeIndex} {R : D.regions}
  {Q : D.OrientedEdgeGraphSubdivision e R
    (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).symm (cut e false) (1 - cut e true)}
  (L : D.CapGraphEndpoint P region chart caps e R (Q.piece Q.firstPiece) false (cut e false))
  (T : D.CapGraphEndpoint P region chart caps e R (Q.piece Q.lastPiece) true (cut e true))
  (K : Q.CutChain L.direction T.direction)
  {r δ : ℝ}



theorem first_cap_cut_velocity_pos_smul
    (B : (Q.piece Q.firstPiece).FixedStripBandFaces (K.graphCuts Q.firstPiece) δ r r)
    (hr : r ≤ 1) :
    ∃ a : ℝ, 0 < a ∧
      coordinateTriangleVelocity
        (B.faces.faceCoordinates (B.faces.firstCell, true))
        (B.faces.faceBasis (B.faces.firstCell, true)) 0 1 = a • L.chordVelocity := by
  have hcoord := linearGraphCoordinates_contMDiff
    (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).symm (Q.piece Q.firstPiece).frame
    (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞))
    (contMDiffOn_chart (I := 𝓡 2) (n := ∞))
  apply coordinateTriangleVelocity_pos_smul_of_image_subset
    ((caps (D.edgeEndpoint e false)).coordinates L.sector)
    (B.faces.faceCoordinates (B.faces.firstCell, true))
    (rightTriangleBasis (caps (D.edgeEndpoint e false)).scale_pos)
    (B.faces.faceBasis (B.faces.firstCell, true))
    ((caps _).coordinates_smooth L.sector) ((caps _).coordinates_smooth_symm L.sector)
    (B.faces.smooth_faceCoordinates hcoord.1 _) (B.faces.smooth_faceCoordinates_symm hcoord.2 _)
    ((caps _).triangle_subset_source L.sector) (B.faces.face_triangle_subset_source _)
    L.chord_indices_ne (by decide : (0 : Fin 3) ≠ 1)
  · rw [funext B.faces.left_endpoint_coordinate_map, B.faces.endpointEdge_image]
    change B.faces.leftCut ⊆ _
    rw [K.first_leftCut_eq_chordSegment L T Q.firstPiece B rfl]
    exact L.chordSegment_subset_coordinate_side hr
  · rw [L.chord_start_eq_tip, B.left_endpoint_coordinate_start (Q.cut_lt Q.firstPiece).le]
    simp only [Q.firstPiece_castSucc, Q.cut_first, edgeFromEndpoint, Bool.false_eq_true, if_false]



theorem last_cap_cut_velocity_pos_smul
    (B : (Q.piece Q.lastPiece).FixedStripBandFaces (K.graphCuts Q.lastPiece) δ r r)
    (hr : r ≤ 1) :
    ∃ a : ℝ, 0 < a ∧
      coordinateTriangleVelocity
        (B.faces.faceCoordinates (B.faces.lastCell, false))
        (B.faces.faceBasis (B.faces.lastCell, false)) 1 2 = a • T.chordVelocity := by
  have hcoord := linearGraphCoordinates_contMDiff
    (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).symm (Q.piece Q.lastPiece).frame
    (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞))
    (contMDiffOn_chart (I := 𝓡 2) (n := ∞))
  apply coordinateTriangleVelocity_pos_smul_of_image_subset
    ((caps (D.edgeEndpoint e true)).coordinates T.sector)
    (B.faces.faceCoordinates (B.faces.lastCell, false))
    (rightTriangleBasis (caps (D.edgeEndpoint e true)).scale_pos)
    (B.faces.faceBasis (B.faces.lastCell, false))
    ((caps _).coordinates_smooth T.sector) ((caps _).coordinates_smooth_symm T.sector)
    (B.faces.smooth_faceCoordinates hcoord.1 _) (B.faces.smooth_faceCoordinates_symm hcoord.2 _)
    ((caps _).triangle_subset_source T.sector) (B.faces.face_triangle_subset_source _)
    T.chord_indices_ne (by decide : (1 : Fin 3) ≠ 2)
  · rw [funext B.faces.right_endpoint_coordinate_map, B.faces.endpointEdge_image]
    change B.faces.rightCut ⊆ _
    rw [K.last_rightCut_eq_chordSegment L T Q.lastPiece B rfl]
    exact T.chordSegment_subset_coordinate_side hr
  · rw [T.chord_start_eq_tip, B.right_endpoint_coordinate_start (Q.cut_lt Q.lastPiece).le]
    simp only [Q.lastPiece_succ, Q.cut_last, edgeFromEndpoint, if_true]



theorem first_cap_cut_cornerAngle (g : RiemannianMetric 2 S)
    (B : (Q.piece Q.firstPiece).FixedStripBandFaces (K.graphCuts Q.firstPiece) δ r r)
    (hr : r ≤ 1) (w : TangentSpace (𝓡 2) (D.edgeFromEndpoint e false (cut e false))) :
    g.cornerAngle
      (B.faces.faceCoordinates (B.faces.firstCell, true)
        (B.faces.faceBasis (B.faces.firstCell, true) 0)) w
      (coordinateTriangleVelocity (B.faces.faceCoordinates (B.faces.firstCell, true))
        (B.faces.faceBasis (B.faces.firstCell, true)) 0 1) =
    g.cornerAngle (D.edgeFromEndpoint e false (cut e false)) w L.chordVelocity := by
  obtain ⟨a, ha, hv⟩ := K.first_cap_cut_velocity_pos_smul L T B hr
  have hpoint : B.faces.faceCoordinates (B.faces.firstCell, true)
      (B.faces.faceBasis (B.faces.firstCell, true) 0) =
        D.edgeFromEndpoint e false (cut e false) := by
    rw [B.left_endpoint_coordinate_start (Q.cut_lt Q.firstPiece).le]
    simp only [Q.firstPiece_castSucc, Q.cut_first, edgeFromEndpoint, Bool.false_eq_true, if_false]
  dsimp only [TangentSpace] at hv w ⊢
  rw [hpoint, hv]
  exact g.cornerAngle_smul_pos_right _ _ _ ha



theorem last_cap_cut_cornerAngle (g : RiemannianMetric 2 S)
    (B : (Q.piece Q.lastPiece).FixedStripBandFaces (K.graphCuts Q.lastPiece) δ r r)
    (hr : r ≤ 1) (w : TangentSpace (𝓡 2) (D.edgeFromEndpoint e true (cut e true))) :
    g.cornerAngle
      (B.faces.faceCoordinates (B.faces.lastCell, false)
        (B.faces.faceBasis (B.faces.lastCell, false) 1)) w
      (coordinateTriangleVelocity (B.faces.faceCoordinates (B.faces.lastCell, false))
        (B.faces.faceBasis (B.faces.lastCell, false)) 1 2) =
    g.cornerAngle (D.edgeFromEndpoint e true (cut e true)) w T.chordVelocity := by
  obtain ⟨a, ha, hv⟩ := K.last_cap_cut_velocity_pos_smul L T B hr
  have hpoint : B.faces.faceCoordinates (B.faces.lastCell, false)
      (B.faces.faceBasis (B.faces.lastCell, false) 1) =
        D.edgeFromEndpoint e true (cut e true) := by
    rw [B.right_endpoint_coordinate_start (Q.cut_lt Q.lastPiece).le]
    simp only [Q.lastPiece_succ, Q.cut_last, edgeFromEndpoint, if_true]
  dsimp only [TangentSpace] at hv w ⊢
  rw [hpoint, hv]
  exact g.cornerAngle_smul_pos_right _ _ _ ha

end FiniteChartRegionDecomposition.OrientedEdgeGraphSubdivision.CutChain

end PoincareConjecture.Topology.Surface
