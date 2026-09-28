import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.Corners
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Frame.Chart
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Boundary.Orientation








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set VectorField
open scoped Manifold ContDiff Bundle Matrix
open Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]



theorem coordinateFrame_positive_at_zero
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hsource : convexHull ℝ (range b) ⊆ F.source)
    (g : RiemannianMetric 2 S)
    (Q : RiemannianMetric.AlignedChartFrame g (coordinateTriangleChart F b)) :
    0 < g.frameOrientation (F (b 0)) (Q.first (F (b 0))) (Q.second (F (b 0)))
      (coordinateTriangleVelocity F b 0 1) (coordinateTriangleVelocity F b 0 2) := by
  have hpoint : F (b 0) ∈ (coordinateTriangleChart F b).source := by
    rw [coordinateTriangleChart_source]
    exact F.map_source (hsource (subset_convexHull ℝ (range b) (mem_range_self 0)))
  rw [coordinateTriangleVelocity_eq_chartField F b hF hFi hsource,
    coordinateTriangleVelocity_eq_chartField F b hF hFi hsource]
  change 0 < g.frameOrientation (F (b 0)) (Q.first (F (b 0))) (Q.second (F (b 0)))
    (mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) (coordinateTriangleChart F b)
      (fun _ => ((1, 0) : ℝ × ℝ) - (0, 0)) (F (b 0)))
    (mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) (coordinateTriangleChart F b)
      (fun _ => ((0, 1) : ℝ × ℝ) - (0, 0)) (F (b 0)))
  simp only [show ((0, 0) : ℝ × ℝ) = 0 from rfl, sub_zero]
  exact Q.positive _ hpoint

section Rectangle

variable (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
  (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
  (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
  {a b c d : ℝ} (hab : a < b) (hcd : c < d)
  (hrect : {z : EuclideanSpace ℝ (Fin 2) | z 0 ∈ Icc a b ∧ z 1 ∈ Icc c d} ⊆ F.source)
  (g : RiemannianMetric 2 S)
  (Q : RiemannianMetric.AlignedChartFrame g
    (coordinateTriangleChart F (rectangleLowerBasis hab hcd)))
  (R : RiemannianMetric.AlignedChartFrame g
    (coordinateTriangleChart F (rectangleUpperBasis hab hcd)))

include hF hFi hrect in

theorem rectangle_frameOrientation_zero :
    let y := F !₂[a, c]
    g.frameOrientation y (Q.first y) (Q.second y) (R.first y) (R.second y) = -1 := by
  let y := F !₂[a, c]
  have hlower : convexHull ℝ (range (rectangleLowerBasis hab hcd)) ⊆ F.source := by
    apply subset_trans _ hrect
    rw [← rectangle_triangle_union hab hcd]
    exact subset_union_left
  have hupper : convexHull ℝ (range (rectangleUpperBasis hab hcd)) ⊆ F.source := by
    apply subset_trans _ hrect
    rw [← rectangle_triangle_union hab hcd]
    exact subset_union_right
  have hy : y ∈ F.target := F.map_source (hrect (by simp [hab.le, hcd.le]))
  have hyQ : y ∈ (coordinateTriangleChart F (rectangleLowerBasis hab hcd)).source := by
    rwa [coordinateTriangleChart_source]
  have hyR : y ∈ (coordinateTriangleChart F (rectangleUpperBasis hab hcd)).source := by
    rwa [coordinateTriangleChart_source]
  have hpos := coordinateFrame_positive_at_zero F _ hF hFi hlower g Q
  have hposR := coordinateFrame_positive_at_zero F _ hF hFi hupper g R
  have hdiag := rectangle_diagonal_velocity_zero F hF hab hcd hrect
  let v : TangentSpace (𝓡 2) y := coordinateTriangleVelocity F (rectangleLowerBasis hab hcd) 0 1
  let w : TangentSpace (𝓡 2) y := coordinateTriangleVelocity F (rectangleUpperBasis hab hcd) 0 1
  let z : TangentSpace (𝓡 2) y := coordinateTriangleVelocity F (rectangleLowerBasis hab hcd) 0 2
  change 0 < g.frameOrientation y (Q.first y) (Q.second y) v z at hpos
  change 0 < g.frameOrientation y (R.first y) (R.second y) w z at hposR
  have hz : z = v + w := by
    dsimp only [TangentSpace] at hdiag ⊢
    simpa only [HAdd.hAdd] using hdiag
  have hchange := g.frameOrientation_change y (Q.first y) (Q.second y)
    (R.unit_first y hyR) (R.unit_second y hyR) (R.orthogonal y hyR) w z
  have hsq := g.frameOrientation_sq y
    (Q.unit_first y hyQ) (Q.unit_second y hyQ) (Q.orthogonal y hyQ)
    (R.unit_first y hyR) (R.unit_second y hyR) (R.orthogonal y hyR)
  have hneg : g.frameOrientation y (Q.first y) (Q.second y) w z =
      -g.frameOrientation y (Q.first y) (Q.second y) v z := by
    rw [hz]
    simp only [RiemannianMetric.frameOrientation, map_add, add_apply]
    ring
  rw [hneg] at hchange
  dsimp only
  nlinarith

include hF hFi hrect in

theorem rectangle_frameOrientation_diagonal :
    ∀ t ∈ Icc (0 : ℝ) 1,
      let y := F (AffineMap.lineMap (!₂[a, c] : EuclideanSpace ℝ (Fin 2)) !₂[b, d] t)
      g.frameOrientation y (Q.first y) (Q.second y) (R.first y) (R.second y) = -1 := by
  let γ := fun t : ℝ =>
    F (AffineMap.lineMap (!₂[a, c] : EuclideanSpace ℝ (Fin 2)) !₂[b, d] t)
  have hsource : MapsTo (AffineMap.lineMap (!₂[a, c] : EuclideanSpace ℝ (Fin 2)) !₂[b, d])
      (Icc (0 : ℝ) 1) F.source := by
    intro t ht
    apply hrect
    have hconv : Convex ℝ {z : EuclideanSpace ℝ (Fin 2) |
        z 0 ∈ Icc a b ∧ z 1 ∈ Icc c d} := by
      exact ((convex_Icc a b).prod (convex_Icc c d)).linear_preimage
        collarParameterEquiv.toLinearMap
    exact hconv.lineMap_mem (by simp [hab.le, hcd.le]) (by simp [hab.le, hcd.le]) ht
  have hγ : ContinuousOn γ (Icc (0 : ℝ) 1) :=
    F.continuousOn.comp (AffineMap.contDiff_lineMap (n := ∞) _ _).continuous.continuousOn hsource
  have hγU : MapsTo γ (Icc (0 : ℝ) 1) F.target := fun t ht => F.map_source (hsource ht)
  obtain ⟨δ, _, hδ⟩ := g.exists_frameOrientation_sign_on_curve
    (by simpa only [coordinateTriangleChart_source] using Q.smooth_first)
    (by simpa only [coordinateTriangleChart_source] using Q.smooth_second)
    (by simpa only [coordinateTriangleChart_source] using R.smooth_first)
    (by simpa only [coordinateTriangleChart_source] using R.smooth_second)
    (by simpa only [coordinateTriangleChart_source] using Q.unit_first)
    (by simpa only [coordinateTriangleChart_source] using Q.unit_second)
    (by simpa only [coordinateTriangleChart_source] using Q.orthogonal)
    (by simpa only [coordinateTriangleChart_source] using R.unit_first)
    (by simpa only [coordinateTriangleChart_source] using R.unit_second)
    (by simpa only [coordinateTriangleChart_source] using R.orthogonal)
    isPreconnected_Icc hγ hγU
  have hδ0 := hδ 0 (by simp)
  have hγ0 : γ 0 = F !₂[a, c] := by simp [γ]
  rw [hγ0, rectangle_frameOrientation_zero F hF hFi hab hcd hrect g Q R] at hδ0
  intro t ht
  exact (hδ t ht).trans hδ0.symm

end Rectangle

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

theorem frameOrientation_diagonal (g : RiemannianMetric 2 S)
    (Q : RiemannianMetric.AlignedChartFrame g
      (coordinateTriangleChart (B.faceCoordinates hU hlo hhi) (B.faceBasis false)))
    (R : RiemannianMetric.AlignedChartFrame g
      (coordinateTriangleChart (B.faceCoordinates hU hlo hhi) (B.faceBasis true))) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      let y := B.faceCoordinates hU hlo hhi
        (AffineMap.lineMap (!₂[a, 0] : EuclideanSpace ℝ (Fin 2)) !₂[b, 1] t)
      g.frameOrientation y (Q.first y) (Q.second y) (R.first y) (R.second y) = -1 :=
  rectangle_frameOrientation_diagonal (B.faceCoordinates hU hlo hhi)
    (B.smooth_faceCoordinates hU hlo hhi hF) (B.smooth_faceCoordinates_symm hU hlo hhi hFi)
    hab zero_lt_one (B.rectangle_subset_faceCoordinates_source hU hlo hhi hI) g Q R

end SmoothGraphBandPair

end PoincareConjecture.Topology.Surface
