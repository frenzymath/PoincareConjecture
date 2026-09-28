import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.CoordinateFormula
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Boundary.CapAngles







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set VectorField
open scoped Manifold ContDiff Bundle
open Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface.ChartCircleArrangementVertexPatch.VertexCapFaces

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
  {r : S → ℝ} {p : S} {P : ChartCircleArrangementVertexPatch r p} {x : Bool × Bool → S}
  (B : VertexCapFaces P x)


noncomputable def firstChartField (i : Bool × Bool) (y : S) : TangentSpace (𝓡 2) y :=
  mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ)
    (coordinateTriangleChart (B.coordinates i) (rightTriangleBasis B.scale_pos))
    (fun _ => (1, 0)) y


noncomputable def secondChartField (i : Bool × Bool) (y : S) : TangentSpace (𝓡 2) y :=
  mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ)
    (coordinateTriangleChart (B.coordinates i) (rightTriangleBasis B.scale_pos))
    (fun _ => (0, 1)) y


noncomputable def secondUnitField (g : RiemannianMetric 2 S) (i : Bool × Bool) (y : S) :
    TangentSpace (𝓡 2) y :=
  (Real.sqrt (g.inner y (B.secondChartField i y) (B.secondChartField i y)))⁻¹ •
    B.secondChartField i y

theorem secondUnitField_smooth (g : RiemannianMetric 2 S) (i : Bool × Bool) :
    ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% (B.secondUnitField g i))
      (B.coordinates i).target := by
  have h := (LeviCivitaData.normalized_chartField_properties g
    (coordinateTriangleChart (B.coordinates i) (rightTriangleBasis B.scale_pos))
    (coordinateTriangleChart_smooth _ _ (B.coordinates_smooth_symm i))
    (coordinateTriangleChart_smooth_symm _ _ (B.coordinates_smooth i))
    (v := (0, 1)) (by norm_num)).1
  simpa only [coordinateTriangleChart_source, secondUnitField, secondChartField] using h


theorem first_chart_map (i : Bool × Bool) (t : ℝ) :
    (coordinateTriangleChart (B.coordinates i) (rightTriangleBasis B.scale_pos)).symm (t, 0) =
      ((B.face i).boundary 2).map t := by
  rw [B.boundary_map]
  have h := coordinateTriangleChart_side (B.coordinates i) (rightTriangleBasis B.scale_pos) 0 1 t
  have hline : AffineMap.lineMap (standardTriangleVertex 0) (standardTriangleVertex 1) t =
      (t, 0) := by
    simp [standardTriangleVertex, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  rw [hline] at h
  convert h using 1
  change B.coordinates i (affineChartSegment (rightTriangleBasis B.scale_pos 0)
    (rightTriangleBasis B.scale_pos 1) t) = _
  simp only [affineChartSegment, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm]


theorem second_chart_map (i : Bool × Bool) (t : ℝ) :
    (coordinateTriangleChart (B.coordinates i) (rightTriangleBasis B.scale_pos)).symm (0, t) =
      ((B.face i).boundary 1).map t := by
  rw [B.boundary_map]
  have h := coordinateTriangleChart_side (B.coordinates i) (rightTriangleBasis B.scale_pos) 0 2 t
  have hline : AffineMap.lineMap (standardTriangleVertex 0) (standardTriangleVertex 2) t =
      (0, t) := by
    change AffineMap.lineMap ((0, 0) : ℝ × ℝ) (0, 1) t = (0, t)
    simp [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  rw [hline] at h
  convert h using 1
  simp [affineChartSegment, AffineMap.lineMap_apply, add_comm]

theorem first_chart_velocity (i : Bool × Bool) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    let e := coordinateTriangleChart (B.coordinates i) (rightTriangleBasis B.scale_pos)
    let γ := ((B.face i).boundary 2).map
    ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 2) ∞ γ t ∧
      mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1 =
        mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (1, 0)) (γ t) := by
  let e := coordinateTriangleChart (B.coordinates i) (rightTriangleBasis B.scale_pos)
  have ht' : ((0, 0) : ℝ × ℝ) + t • (1, 0) ∈ e.target := by
    apply coordinateTriangleChart_target _ _ (B.triangle_subset_source i)
    simpa using And.intro ht.1 (And.intro (le_refl (0 : ℝ)) ht.2)
  have h := LeviCivitaData.mfderiv_chart_line e
    (coordinateTriangleChart_smooth _ _ (B.coordinates_smooth_symm i))
    (coordinateTriangleChart_smooth_symm _ _ (B.coordinates_smooth i)) (0, 0) (1, 0) ht'
  have hcurve : (fun s : ℝ => e.symm ((0, 0) + s • (1, 0))) =
      ((B.face i).boundary 2).map := by
    funext s
    have hs : ((0, 0) : ℝ × ℝ) + s • (1, 0) = (s, 0) := by ext <;> simp
    rw [hs]
    exact B.first_chart_map i s
  have hpoint : e.symm ((0, 0) + t • (1, 0)) = ((B.face i).boundary 2).map t :=
    congrFun hcurve t
  dsimp only [TangentSpace] at h ⊢
  rw [hcurve, hpoint] at h
  exact h

theorem second_chart_velocity (i : Bool × Bool) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    let γ := ((B.face i).boundary 1).map
    ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 2) ∞ γ t ∧
      mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1 = B.secondChartField i (γ t) := by
  let e := coordinateTriangleChart (B.coordinates i) (rightTriangleBasis B.scale_pos)
  have ht' : ((0, 0) : ℝ × ℝ) + t • (0, 1) ∈ e.target := by
    apply coordinateTriangleChart_target _ _ (B.triangle_subset_source i)
    simpa using And.intro (le_refl (0 : ℝ)) ht
  have h := LeviCivitaData.mfderiv_chart_line e
    (coordinateTriangleChart_smooth _ _ (B.coordinates_smooth_symm i))
    (coordinateTriangleChart_smooth_symm _ _ (B.coordinates_smooth i)) (0, 0) (0, 1) ht'
  have hcurve : (fun s : ℝ => e.symm ((0, 0) + s • (0, 1))) =
      ((B.face i).boundary 1).map := by
    funext s
    have hs : ((0, 0) : ℝ × ℝ) + s • (0, 1) = (0, s) := by ext <;> simp
    rw [hs]
    exact B.second_chart_map i s
  have hpoint : e.symm ((0, 0) + t • (0, 1)) = ((B.face i).boundary 1).map t :=
    congrFun hcurve t
  dsimp only [TangentSpace] at h ⊢
  rw [hcurve, hpoint] at h
  exact h

theorem coordinate_vertex_zero (i : Bool × Bool) :
    B.coordinates i (rightTriangleBasis B.scale_pos 0) = p := by
  have h := B.first_map i 0 (by simp)
  rw [B.boundary_map] at h
  have hz : P.sectorCoordinates i (0, 0) = p := P.sectorCoordinates_zero i
  simpa [Function.comp_def, affineChartSegment, hz] using h

theorem coordinate_side_velocity (i : Bool × Bool) (k : Fin 3) :
    coordinateTriangleVelocity (B.coordinates i) (rightTriangleBasis B.scale_pos)
        (k.succAbove 0) (k.succAbove 1) =
      mfderivWithin 𝓘(ℝ, ℝ) (𝓡 2) ((B.face i).boundary k).map (Icc (0 : ℝ) 1) 0 1 := by
  rw [coordinateTriangleVelocity_eq_mfderivWithin _ _
    (B.coordinates_smooth i) (B.triangle_subset_source i), B.boundary_map]
  have hcurve : (fun t : ℝ => B.coordinates i
      (AffineMap.lineMap (rightTriangleBasis B.scale_pos (k.succAbove 0))
        (rightTriangleBasis B.scale_pos (k.succAbove 1)) t)) =
      B.coordinates i ∘ affineChartSegment
        (rightTriangleBasis B.scale_pos (k.succAbove 0))
        (rightTriangleBasis B.scale_pos (k.succAbove 1)) := by
    funext t
    simp only [Function.comp_apply, affineChartSegment, AffineMap.lineMap_apply,
      vsub_eq_sub, vadd_eq_add, add_comm]
  rw [hcurve]
  rfl

theorem coordinate_angle_zero (g : RiemannianMetric 2 S) (i : Bool × Bool) :
    coordinateTriangleAngle g (B.coordinates i) (rightTriangleBasis B.scale_pos) 0 =
      g.cornerAngle p
        (mfderivWithin 𝓘(ℝ, ℝ) (𝓡 2) ((B.face i).boundary 2).map (Icc (0 : ℝ) 1) 0 1)
        (mfderivWithin 𝓘(ℝ, ℝ) (𝓡 2) ((B.face i).boundary 1).map (Icc (0 : ℝ) 1) 0 1) := by
  have hfirst := B.coordinate_side_velocity i 2
  have hsecond := B.coordinate_side_velocity i 1
  change coordinateTriangleVelocity (B.coordinates i) (rightTriangleBasis B.scale_pos) 0 1 = _
    at hfirst
  change coordinateTriangleVelocity (B.coordinates i) (rightTriangleBasis B.scale_pos) 0 2 = _
    at hsecond
  unfold coordinateTriangleAngle
  change g.cornerAngle (B.coordinates i (rightTriangleBasis B.scale_pos 0))
    (coordinateTriangleVelocity (B.coordinates i) (rightTriangleBasis B.scale_pos) 0 1)
    (coordinateTriangleVelocity (B.coordinates i) (rightTriangleBasis B.scale_pos) 0 2) = _
  dsimp only [TangentSpace] at hfirst hsecond ⊢
  rw [hfirst, hsecond, B.coordinate_vertex_zero]


theorem sum_coordinate_angles (g : RiemannianMetric 2 S) :
    (∑ i : Bool, ∑ j : Bool,
      coordinateTriangleAngle g (B.coordinates (i, j)) (rightTriangleBasis B.scale_pos) 0) =
      2 * Real.pi := by
  simp_rw [B.coordinate_angle_zero]
  exact B.sum_corner_angles g

end PoincareConjecture.Topology.Surface.ChartCircleArrangementVertexPatch.VertexCapFaces
