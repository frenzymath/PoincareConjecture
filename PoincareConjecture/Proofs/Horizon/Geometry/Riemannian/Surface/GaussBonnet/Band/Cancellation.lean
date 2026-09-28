import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.Orientation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Boundary.Locality








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set VectorField MeasureTheory
open scoped Manifold ContDiff Bundle Matrix Interval Topology
open Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]


noncomputable def coordinateTriangleSecondField
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (y : S) : TangentSpace (𝓡 2) y :=
  mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) (coordinateTriangleChart F b) (fun _ => (0, 1)) y

noncomputable def coordinateTriangleSecondUnitField (g : RiemannianMetric 2 S)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (y : S) : TangentSpace (𝓡 2) y :=
  (Real.sqrt (g.inner y (coordinateTriangleSecondField F b y)
    (coordinateTriangleSecondField F b y)))⁻¹ • coordinateTriangleSecondField F b y

theorem coordinateTriangleSecondUnitField_smooth (g : RiemannianMetric 2 S)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target) :
    ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞
      (T% (coordinateTriangleSecondUnitField g F b)) F.target := by
  have h := (LeviCivitaData.normalized_chartField_properties g (coordinateTriangleChart F b)
    (coordinateTriangleChart_smooth F b hFi) (coordinateTriangleChart_smooth_symm F b hF)
    (v := (0, 1)) (by norm_num)).1
  simpa only [coordinateTriangleSecondUnitField, coordinateTriangleSecondField,
    coordinateTriangleChart_source] using h

omit [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S] in
theorem coordinateTriangle_second_map
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) (t : ℝ) :
    (coordinateTriangleChart F b).symm (0, t) = F (AffineMap.lineMap (b 0) (b 2) t) := by
  have h := coordinateTriangleChart_side F b 0 2 t
  have he : AffineMap.lineMap (standardTriangleVertex 0) (standardTriangleVertex 2) t =
      (0, t) := by
    change AffineMap.lineMap ((0, 0) : ℝ × ℝ) (0, 1) t = (0, t)
    simp [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  rwa [he] at h

omit [IsManifold (𝓡 2) ∞ S] in
theorem coordinateTriangle_second_velocity
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hsource : convexHull ℝ (range b) ⊆ F.source)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    let γ := fun s : ℝ => F (AffineMap.lineMap (b 0) (b 2) s)
    ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 2) ∞ γ t ∧
      mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1 = coordinateTriangleSecondField F b (γ t) := by
  let e := coordinateTriangleChart F b
  have ht' : ((0, 0) : ℝ × ℝ) + t • (0, 1) ∈ e.target := by
    apply coordinateTriangleChart_target F b hsource
    simpa using And.intro (le_refl (0 : ℝ)) ht
  have h := LeviCivitaData.mfderiv_chart_line e
    (coordinateTriangleChart_smooth F b hFi) (coordinateTriangleChart_smooth_symm F b hF)
    (0, 0) (0, 1) ht'
  have hcurve : (fun s : ℝ => e.symm ((0, 0) + s • (0, 1))) =
      fun s : ℝ => F (AffineMap.lineMap (b 0) (b 2) s) := by
    funext s
    have hs : ((0, 0) : ℝ × ℝ) + s • (0, 1) = (0, s) := by ext <;> simp
    rw [hs]
    exact coordinateTriangle_second_map F b s
  have hpoint := congrFun hcurve t
  dsimp only [TangentSpace] at h ⊢
  rw [hcurve, hpoint] at h
  exact h

section Rectangle

variable (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
  (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
  (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
  {a b c d : ℝ} (hab : a < b) (hcd : c < d)
  (hrect : {z : EuclideanSpace ℝ (Fin 2) | z 0 ∈ Icc a b ∧ z 1 ∈ Icc c d} ⊆ F.source)
  {g : RiemannianMetric 2 S} (D : LeviCivitaData g)
  (Q : RiemannianMetric.AlignedChartFrame g
    (coordinateTriangleChart F (rectangleLowerBasis hab hcd)))
  (R : RiemannianMetric.AlignedChartFrame g
    (coordinateTriangleChart F (rectangleUpperBasis hab hcd)))

include hF hFi hrect in

theorem integral_rectangle_diagonal_pair_eq_zero :
    let γ := fun t : ℝ => F (AffineMap.lineMap (!₂[a, c] : EuclideanSpace ℝ (Fin 2)) !₂[b, d] t)
    (∫ t in (0 : ℝ)..1, D.surfaceTurningForm Q.first Q.second
      (coordinateTriangleSecondUnitField g F (rectangleLowerBasis hab hcd))
      (coordinateTriangleSecondField F (rectangleLowerBasis hab hcd)) (γ t)) +
    (∫ t in (0 : ℝ)..1, D.surfaceTurningForm R.first R.second
      (coordinateTriangleSecondUnitField g F (rectangleUpperBasis hab hcd))
      (coordinateTriangleSecondField F (rectangleUpperBasis hab hcd)) (γ t)) = 0 := by
  let γ := fun t : ℝ => F (AffineMap.lineMap (!₂[a, c] : EuclideanSpace ℝ (Fin 2)) !₂[b, d] t)
  let bL := rectangleLowerBasis hab hcd
  let bU := rectangleUpperBasis hab hcd
  have hlower : convexHull ℝ (range bL) ⊆ F.source := by
    apply subset_trans _ hrect
    rw [← rectangle_triangle_union hab hcd]
    exact subset_union_left
  have hupper : convexHull ℝ (range bU) ⊆ F.source := by
    apply subset_trans _ hrect
    rw [← rectangle_triangle_union hab hcd]
    exact subset_union_right
  have htarget (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ t ∈ F.target := by
    apply F.map_source
    apply hlower
    exact (convex_convexHull ℝ (range bL)).lineMap_mem
      (subset_convexHull ℝ (range bL) (mem_range_self 0))
      (subset_convexHull ℝ (range bL) (mem_range_self 2)) ht
  have hvelocity (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      coordinateTriangleSecondField F bU (γ t) = coordinateTriangleSecondField F bL (γ t) := by
    exact (coordinateTriangle_second_velocity F bU hF hFi hupper ht).2.symm.trans
      (coordinateTriangle_second_velocity F bL hF hFi hlower ht).2
  have hpoint (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      D.surfaceTurningForm R.first R.second (coordinateTriangleSecondUnitField g F bU)
          (coordinateTriangleSecondField F bU) (γ t) =
        -D.surfaceTurningForm Q.first Q.second (coordinateTriangleSecondUnitField g F bL)
          (coordinateTriangleSecondField F bL) (γ t) := by
    have ht' := Ioo_subset_Icc_self ht
    have htg := htarget t ht'
    have hcurve := coordinateTriangle_second_velocity F bL hF hFi hlower ht'
    change ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 2) ∞ γ t ∧
      mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1 = coordinateTriangleSecondField F bL (γ t) at hcurve
    have hfield := hvelocity t ht'
    have heq : ∀ᶠ s in 𝓝 t, coordinateTriangleSecondUnitField g F bU (γ s) =
        coordinateTriangleSecondUnitField g F bL (γ s) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      simp only [coordinateTriangleSecondUnitField, hvelocity s (Ioo_subset_Icc_self hs)]
    have hlocal := D.surfaceTurningForm_eq_of_eventuallyEq_along_curve
      (hcurve.1.mdifferentiableAt (by simp)) Q.first Q.second
      (((coordinateTriangleSecondUnitField_smooth g F bU hF hFi).contMDiffAt
        (F.open_target.mem_nhds htg)).mdifferentiableAt (by simp))
      (((coordinateTriangleSecondUnitField_smooth g F bL hF hFi).contMDiffAt
        (F.open_target.mem_nhds htg)).mdifferentiableAt (by simp))
      heq (hfield.trans hcurve.2.symm) hcurve.2.symm
    have htgQ : γ t ∈ (coordinateTriangleChart F bL).source := by
      rwa [coordinateTriangleChart_source]
    rw [D.surfaceTurningForm_change_frame Q.first Q.second R.first R.second
      (coordinateTriangleSecondUnitField g F bU) (coordinateTriangleSecondField F bU) (γ t)
      (Q.unit_first _ htgQ) (Q.unit_second _ htgQ) (Q.orthogonal _ htgQ)]
    change g.frameOrientation (γ t) (Q.first (γ t)) (Q.second (γ t))
      (R.first (γ t)) (R.second (γ t)) * _ = _
    rw [rectangle_frameOrientation_diagonal F hF hFi hab hcd hrect g Q R t ht',
      hlocal, neg_one_mul]
  have hint : (∫ t in (0 : ℝ)..1, D.surfaceTurningForm R.first R.second
      (coordinateTriangleSecondUnitField g F bU) (coordinateTriangleSecondField F bU) (γ t)) =
      -(∫ t in (0 : ℝ)..1, D.surfaceTurningForm Q.first Q.second
        (coordinateTriangleSecondUnitField g F bL) (coordinateTriangleSecondField F bL) (γ t)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
    intro t ht
    exact hpoint t ht
  dsimp only
  rw [hint]
  exact add_neg_cancel _

end Rectangle

end PoincareConjecture.Topology.Surface
