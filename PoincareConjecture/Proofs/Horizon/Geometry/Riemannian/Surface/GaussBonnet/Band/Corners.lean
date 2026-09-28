import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.MetricCorners
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.BoundaryRectangles
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Bands.Coordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set VectorField
open scoped Manifold ContDiff Bundle Matrix
open Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]

section Rectangle

variable (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
  (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
  (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
  {a b c d : ℝ} (hab : a < b) (hcd : c < d)
  (hrect : {z : EuclideanSpace ℝ (Fin 2) | z 0 ∈ Icc a b ∧ z 1 ∈ Icc c d} ⊆ F.source)

include hrect in
omit [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S] in
private theorem lower_source_subset :
    convexHull ℝ (range (rectangleLowerBasis hab hcd)) ⊆ F.source := by
  apply subset_trans _ hrect
  rw [← rectangle_triangle_union hab hcd]
  exact subset_union_left

include hrect in
omit [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S] in
private theorem upper_source_subset :
    convexHull ℝ (range (rectangleUpperBasis hab hcd)) ⊆ F.source := by
  apply subset_trans _ hrect
  rw [← rectangle_triangle_union hab hcd]
  exact subset_union_right

include hF hrect in
omit [IsManifold (𝓡 2) ∞ S] in

theorem rectangle_diagonal_velocity_zero :
    coordinateTriangleVelocity F (rectangleLowerBasis hab hcd) 0 2 =
      @Add.add (TangentSpace (𝓡 2) (F !₂[a, c])) inferInstance
        (coordinateTriangleVelocity F (rectangleLowerBasis hab hcd) 0 1)
        (coordinateTriangleVelocity F (rectangleUpperBasis hab hcd) 0 1) := by
  dsimp only [TangentSpace]
  rw [coordinateTriangleVelocity_eq_differential F _ hF (lower_source_subset F hab hcd hrect),
    coordinateTriangleVelocity_eq_differential F _ hF (lower_source_subset F hab hcd hrect),
    coordinateTriangleVelocity_eq_differential F _ hF (upper_source_subset F hab hcd hrect)]
  change mfderiv (𝓡 2) (𝓡 2) F !₂[a, c] (!₂[b, d] - !₂[a, c]) =
    mfderiv (𝓡 2) (𝓡 2) F !₂[a, c] (!₂[b, c] - !₂[a, c]) +
    mfderiv (𝓡 2) (𝓡 2) F !₂[a, c] (!₂[a, d] - !₂[a, c])
  rw [← map_add]
  congr 1
  dsimp only [TangentSpace]
  ext k
  fin_cases k <;> simp

include hF hrect in
omit [IsManifold (𝓡 2) ∞ S] in

theorem rectangle_diagonal_velocity_two :
    coordinateTriangleVelocity F (rectangleLowerBasis hab hcd) 2 0 =
      @Add.add (TangentSpace (𝓡 2) (F !₂[b, d])) inferInstance
        (coordinateTriangleVelocity F (rectangleLowerBasis hab hcd) 2 1)
        (coordinateTriangleVelocity F (rectangleUpperBasis hab hcd) 2 1) := by
  dsimp only [TangentSpace]
  rw [coordinateTriangleVelocity_eq_differential F _ hF (lower_source_subset F hab hcd hrect),
    coordinateTriangleVelocity_eq_differential F _ hF (lower_source_subset F hab hcd hrect),
    coordinateTriangleVelocity_eq_differential F _ hF (upper_source_subset F hab hcd hrect)]
  change mfderiv (𝓡 2) (𝓡 2) F !₂[b, d] (!₂[a, c] - !₂[b, d]) =
    mfderiv (𝓡 2) (𝓡 2) F !₂[b, d] (!₂[b, c] - !₂[b, d]) +
    mfderiv (𝓡 2) (𝓡 2) F !₂[b, d] (!₂[a, d] - !₂[b, d])
  rw [← map_add]
  congr 1
  dsimp only [TangentSpace]
  ext k
  fin_cases k <;> simp

include hF hFi hrect in

theorem rectangle_cornerAngle_split_zero (g : RiemannianMetric 2 S) :
    coordinateTriangleAngle g F (rectangleLowerBasis hab hcd) 0 +
      coordinateTriangleAngle g F (rectangleUpperBasis hab hcd) 0 =
      g.cornerAngle (F !₂[a, c])
        (coordinateTriangleVelocity F (rectangleLowerBasis hab hcd) 0 1)
        (coordinateTriangleVelocity F (rectangleUpperBasis hab hcd) 0 1) := by
  have hdiag := rectangle_diagonal_velocity_zero F hF hab hcd hrect
  have hne := coordinateTriangleVelocity_ne_zero F (rectangleLowerBasis hab hcd)
    hF hFi (lower_source_subset F hab hcd hrect) (i := 0) (j := 2) (by decide)
  dsimp only [TangentSpace] at hdiag hne ⊢
  have hsame : coordinateTriangleVelocity F (rectangleUpperBasis hab hcd) 0 2 =
      coordinateTriangleVelocity F (rectangleLowerBasis hab hcd) 0 2 := rfl
  change g.cornerAngle (F !₂[a, c])
      (coordinateTriangleVelocity F (rectangleLowerBasis hab hcd) 0 1)
      (coordinateTriangleVelocity F (rectangleLowerBasis hab hcd) 0 2) +
    g.cornerAngle (F !₂[a, c])
      (coordinateTriangleVelocity F (rectangleUpperBasis hab hcd) 0 1)
      (coordinateTriangleVelocity F (rectangleUpperBasis hab hcd) 0 2) = _
  rw [hsame, g.cornerAngle_comm (F !₂[a, c])
    (coordinateTriangleVelocity F (rectangleUpperBasis hab hcd) 0 1)
    (coordinateTriangleVelocity F (rectangleLowerBasis hab hcd) 0 2)]
  have h := g.cornerAngle_split_of_nonneg_combination (F !₂[a, c])
    (coordinateTriangleVelocity F (rectangleLowerBasis hab hcd) 0 1)
    (coordinateTriangleVelocity F (rectangleUpperBasis hab hcd) 0 1)
    (a := 1) (b := 1) (by norm_num) (by norm_num) (by
      rw [hdiag] at hne
      dsimp only [TangentSpace] at *
      simpa only [one_smul, HAdd.hAdd] using hne)
  rw [hdiag]
  dsimp only [TangentSpace] at h ⊢
  simpa only [one_smul, HAdd.hAdd] using h.symm

include hF hFi hrect in

theorem rectangle_cornerAngle_split_two (g : RiemannianMetric 2 S) :
    coordinateTriangleAngle g F (rectangleLowerBasis hab hcd) 2 +
      coordinateTriangleAngle g F (rectangleUpperBasis hab hcd) 2 =
      g.cornerAngle (F !₂[b, d])
        (coordinateTriangleVelocity F (rectangleLowerBasis hab hcd) 2 1)
        (coordinateTriangleVelocity F (rectangleUpperBasis hab hcd) 2 1) := by
  have hdiag := rectangle_diagonal_velocity_two F hF hab hcd hrect
  have hne := coordinateTriangleVelocity_ne_zero F (rectangleLowerBasis hab hcd)
    hF hFi (lower_source_subset F hab hcd hrect) (i := 2) (j := 0) (by decide)
  dsimp only [TangentSpace] at hdiag hne ⊢
  have hsame : coordinateTriangleVelocity F (rectangleUpperBasis hab hcd) 2 0 =
      coordinateTriangleVelocity F (rectangleLowerBasis hab hcd) 2 0 := rfl
  change g.cornerAngle (F !₂[b, d])
      (coordinateTriangleVelocity F (rectangleLowerBasis hab hcd) 2 0)
      (coordinateTriangleVelocity F (rectangleLowerBasis hab hcd) 2 1) +
    g.cornerAngle (F !₂[b, d])
      (coordinateTriangleVelocity F (rectangleUpperBasis hab hcd) 2 0)
      (coordinateTriangleVelocity F (rectangleUpperBasis hab hcd) 2 1) = _
  rw [hsame, g.cornerAngle_comm (F !₂[b, d]) (coordinateTriangleVelocity F (rectangleLowerBasis hab hcd) 2 0)
    (coordinateTriangleVelocity F (rectangleLowerBasis hab hcd) 2 1)]
  have h := g.cornerAngle_split_of_nonneg_combination (F !₂[b, d])
    (coordinateTriangleVelocity F (rectangleLowerBasis hab hcd) 2 1)
    (coordinateTriangleVelocity F (rectangleUpperBasis hab hcd) 2 1)
    (a := 1) (b := 1) (by norm_num) (by norm_num) (by
      rw [hdiag] at hne
      dsimp only [TangentSpace] at *
      simpa only [one_smul, HAdd.hAdd] using hne)
  rw [hdiag]
  dsimp only [TangentSpace] at h ⊢
  simpa only [one_smul, HAdd.hAdd] using h.symm

end Rectangle

namespace FiniteChartRegionDecomposition.BoundaryRectangle

variable {D : FiniteChartRegionDecomposition (M := S)} {a : D.EdgeIndex}
  (R : D.BoundaryRectangle a)

theorem cornerAngle_split_zero (g : RiemannianMetric 2 S) :
    coordinateTriangleAngle g R.coordinates (R.triangleBasis false) 0 +
      coordinateTriangleAngle g R.coordinates (R.triangleBasis true) 0 =
      g.cornerAngle (R.coordinates !₂[R.left, -R.width / 2])
        (coordinateTriangleVelocity R.coordinates (R.triangleBasis false) 0 1)
        (coordinateTriangleVelocity R.coordinates (R.triangleBasis true) 0 1) :=
  rectangle_cornerAngle_split_zero R.coordinates R.smooth R.smooth_symm R.left_lt_right
    (show -R.width / 2 < R.width / 2 by linarith [R.width_pos]) R.rectangle_subset g

theorem cornerAngle_split_two (g : RiemannianMetric 2 S) :
    coordinateTriangleAngle g R.coordinates (R.triangleBasis false) 2 +
      coordinateTriangleAngle g R.coordinates (R.triangleBasis true) 2 =
      g.cornerAngle (R.coordinates !₂[R.right, R.width / 2])
        (coordinateTriangleVelocity R.coordinates (R.triangleBasis false) 2 1)
        (coordinateTriangleVelocity R.coordinates (R.triangleBasis true) 2 1) :=
  rectangle_cornerAngle_split_two R.coordinates R.smooth R.smooth_symm R.left_lt_right
    (show -R.width / 2 < R.width / 2 by linarith [R.width_pos]) R.rectangle_subset g

end FiniteChartRegionDecomposition.BoundaryRectangle

namespace SmoothGraphBandPair

variable {F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S}
  {lo hi : ℝ → ℝ} {a b : ℝ} {hab : a < b}
  (B : SmoothGraphBandPair F lo hi hab)
  {U : Set ℝ} (hU : IsOpen U)
  (hlo : ContDiffOn ℝ ∞ lo U) (hhi : ContDiffOn ℝ ∞ hi U)
  (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
  (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
  (hI : Icc a b ⊆ U)

include hF hFi hI in

theorem cornerAngle_split_zero (g : RiemannianMetric 2 S) :
    let C := B.faceCoordinates hU hlo hhi
    coordinateTriangleAngle g C (B.faceBasis false) 0 +
      coordinateTriangleAngle g C (B.faceBasis true) 0 =
      g.cornerAngle (C !₂[a, 0])
        (coordinateTriangleVelocity C (B.faceBasis false) 0 1)
        (coordinateTriangleVelocity C (B.faceBasis true) 0 1) :=
  rectangle_cornerAngle_split_zero (B.faceCoordinates hU hlo hhi)
    (B.smooth_faceCoordinates hU hlo hhi hF) (B.smooth_faceCoordinates_symm hU hlo hhi hFi)
    hab zero_lt_one (B.rectangle_subset_faceCoordinates_source hU hlo hhi hI) g

include hF hFi hI in

theorem cornerAngle_split_two (g : RiemannianMetric 2 S) :
    let C := B.faceCoordinates hU hlo hhi
    coordinateTriangleAngle g C (B.faceBasis false) 2 +
      coordinateTriangleAngle g C (B.faceBasis true) 2 =
      g.cornerAngle (C !₂[b, 1])
        (coordinateTriangleVelocity C (B.faceBasis false) 2 1)
        (coordinateTriangleVelocity C (B.faceBasis true) 2 1) :=
  rectangle_cornerAngle_split_two (B.faceCoordinates hU hlo hhi)
    (B.smooth_faceCoordinates hU hlo hhi hF) (B.smooth_faceCoordinates_symm hU hlo hhi hFi)
    hab zero_lt_one (B.rectangle_subset_faceCoordinates_source hU hlo hhi hI) g

end SmoothGraphBandPair

end PoincareConjecture.Topology.Surface
