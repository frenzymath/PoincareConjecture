import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.Assembly

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set VectorField MeasureTheory
open scoped Manifold ContDiff Bundle Matrix Interval
open Poincare.Topology.Plane.Triangles Poincare.Topology.Plane.Curves

namespace PoincareConjecture.Topology.Surface

variable {S : Type*} [TopologicalSpace S]

theorem coordinateTriangle_first_map
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) (t : ℝ) :
    (coordinateTriangleChart F b).symm (t, 0) = F (AffineMap.lineMap (b 0) (b 1) t) := by
  have h := coordinateTriangleChart_side F b 0 1 t
  have he : AffineMap.lineMap (standardTriangleVertex 0) (standardTriangleVertex 1) t =
      (t, 0) := by
    change AffineMap.lineMap ((0, 0) : ℝ × ℝ) (1, 0) t = (t, 0)
    simp [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  rwa [he] at h

theorem coordinateTriangle_chord_map
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) (t : ℝ) :
    (coordinateTriangleChart F b).symm (1 - t, t) = F (AffineMap.lineMap (b 1) (b 2) t) := by
  have h := coordinateTriangleChart_side F b 1 2 t
  have he : AffineMap.lineMap (standardTriangleVertex 1) (standardTriangleVertex 2) t =
      (1 - t, t) := by
    change AffineMap.lineMap ((1, 0) : ℝ × ℝ) (0, 1) t = (1 - t, t)
    ext <;> simp [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    ring
  rwa [he] at h

namespace SmoothGraphBandPair

variable [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
  {F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S}
  {lo hi : ℝ → ℝ} {a b : ℝ} {hab : a < b}
  (B : SmoothGraphBandPair F lo hi hab)
  {U : Set ℝ} (hU : IsOpen U)
  (hlo : ContDiffOn ℝ ∞ lo U) (hhi : ContDiffOn ℝ ∞ hi U)

theorem lower_chart_map (t : ℝ) :
    (coordinateTriangleChart (B.faceCoordinates hU hlo hhi) (B.faceBasis false)).symm
      (t, 0) = (B.lower.boundary 2).map t := by
  rw [coordinateTriangle_first_map, B.lower_edge]
  change F (collarParameterEquiv.symm (graphStripMap lo hi
    (collarParameterEquiv (AffineMap.lineMap (!₂[a, 0] : EuclideanSpace ℝ (Fin 2)) !₂[b, 0] t)))) = _
  have he : collarParameterEquiv
      (AffineMap.lineMap (!₂[a, 0] : EuclideanSpace ℝ (Fin 2)) !₂[b, 0] t) =
      (a + t * (b - a), 0) := by
    ext <;> simp [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, collarParameterEquiv, add_comm]
  rw [he, graphStripMap_lower]

theorem right_chart_map (t : ℝ) :
    (coordinateTriangleChart (B.faceCoordinates hU hlo hhi) (B.faceBasis false)).symm
      (1 - t, t) = (B.lower.boundary 0).map t := by
  rw [coordinateTriangle_chord_map, B.right_edge]
  change F (collarParameterEquiv.symm (graphStripMap lo hi
    (collarParameterEquiv (AffineMap.lineMap (!₂[b, 0] : EuclideanSpace ℝ (Fin 2)) !₂[b, 1] t)))) = _
  have he : collarParameterEquiv
      (AffineMap.lineMap (!₂[b, 0] : EuclideanSpace ℝ (Fin 2)) !₂[b, 1] t) = (b, t) := by
    ext <;> simp [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, collarParameterEquiv]
  rw [he]
  rfl

theorem left_chart_map (t : ℝ) :
    (coordinateTriangleChart (B.faceCoordinates hU hlo hhi) (B.faceBasis true)).symm
      (t, 0) = (B.upper.boundary 2).map t := by
  rw [coordinateTriangle_first_map, B.left_edge]
  change F (collarParameterEquiv.symm (graphStripMap lo hi
    (collarParameterEquiv (AffineMap.lineMap (!₂[a, 0] : EuclideanSpace ℝ (Fin 2)) !₂[a, 1] t)))) = _
  have he : collarParameterEquiv
      (AffineMap.lineMap (!₂[a, 0] : EuclideanSpace ℝ (Fin 2)) !₂[a, 1] t) = (a, t) := by
    ext <;> simp [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, collarParameterEquiv]
  rw [he]
  rfl

theorem upper_chart_map (t : ℝ) :
    (coordinateTriangleChart (B.faceCoordinates hU hlo hhi) (B.faceBasis true)).symm
      (1 - t, t) = (B.upper.boundary 0).map t := by
  rw [coordinateTriangle_chord_map, B.upper_edge]
  change F (collarParameterEquiv.symm (graphStripMap lo hi
    (collarParameterEquiv (AffineMap.lineMap (!₂[a, 1] : EuclideanSpace ℝ (Fin 2)) !₂[b, 1] t)))) = _
  have he : collarParameterEquiv
      (AffineMap.lineMap (!₂[a, 1] : EuclideanSpace ℝ (Fin 2)) !₂[b, 1] t) =
      (a + t * (b - a), 1) := by
    ext <;> simp [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, collarParameterEquiv, add_comm]
  rw [he, graphStripMap_upper]

theorem first_chart_map (i : Bool) (t : ℝ) :
    (coordinateTriangleChart (B.faceCoordinates hU hlo hhi) (B.faceBasis i)).symm
      (t, 0) = ((B.face i).boundary 2).map t := by
  cases i
  · exact B.lower_chart_map hU hlo hhi t
  · exact B.left_chart_map hU hlo hhi t

theorem chord_chart_map (i : Bool) (t : ℝ) :
    (coordinateTriangleChart (B.faceCoordinates hU hlo hhi) (B.faceBasis i)).symm
      (1 - t, t) = ((B.face i).boundary 0).map t := by
  cases i
  · exact B.right_chart_map hU hlo hhi t
  · exact B.upper_chart_map hU hlo hhi t

variable [MeasurableSpace S] [BorelSpace S] [T3Space S]
  (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
  (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
  {g : RiemannianMetric 2 S}

theorem gaussBonnet_band_boundary (hI : Icc a b ⊆ U) (D : LeviCivitaData g) :
    let C := B.faceCoordinates hU hlo hhi
    let e := fun i => coordinateTriangleChart C (B.faceBasis i)
    let Q := B.alignedFrame hU hlo hhi hF hFi g
    let X := fun i => mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) (e i) (fun _ => (1, 0))
    let V := fun i => mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) (e i) (fun _ => (-1, 1))
    let W := fun i y => (Real.sqrt (g.inner y (V i y) (V i y)))⁻¹ • V i y
    (∫ y in F '' coordinateGraphBand lo hi a b, D.scalarCurvature y ∂g.volumeMeasure) +
      2 * ((∫ t in (0 : ℝ)..1, D.surfaceTurningForm (Q false).first (Q false).second
          (Q false).first (X false) ((B.lower.boundary 2).map t)) +
        (∫ t in (0 : ℝ)..1, D.surfaceTurningForm (Q false).first (Q false).second
          (W false) (V false) ((B.lower.boundary 0).map t)) +
        (∫ t in (0 : ℝ)..1, D.surfaceTurningForm (Q true).first (Q true).second
          (Q true).first (X true) ((B.upper.boundary 2).map t)) +
        (∫ t in (0 : ℝ)..1, D.surfaceTurningForm (Q true).first (Q true).second
          (W true) (V true) ((B.upper.boundary 0).map t))) +
      2 * (4 * Real.pi - B.outerCornerSum hU hlo hhi g) = 4 * Real.pi := by
  have h := B.gaussBonnet_band hU hlo hhi hF hFi hI D
  dsimp only at h ⊢
  simp only [Fintype.sum_bool, B.lower_chart_map, B.right_chart_map,
    B.left_chart_map, B.upper_chart_map] at h
  linarith only [h]

end SmoothGraphBandPair

end PoincareConjecture.Topology.Surface
