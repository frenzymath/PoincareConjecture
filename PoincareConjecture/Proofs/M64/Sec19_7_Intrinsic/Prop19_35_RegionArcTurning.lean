import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BoundaryArcTurning
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionBoundaryTurning
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_GeodesicArcSideTurning
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.BoundarySum















noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Topology ContDiff Manifold Bundle
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

private theorem cyclic_side_image
    {I : Type*} (face : I → SmoothFace AnnulusCoordinates)
    (F : I → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : I → AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hboundary : ∀ i k, ((face i).boundary k).map = F i ∘
      affineChartSegment (b i (k.succAbove 0)) (b i (k.succAbove 1)))
    (i : I) (k : Fin 3) :
    (fun t : ℝ => F i (AffineMap.lineMap (b i (k + 1)) (b i ((k + 1) + 1)) t)) ''
      Icc (0 : ℝ) 1 = ((face i).boundary k).map '' Icc (0 : ℝ) 1 := by
  rw [coordinateTriangle_cyclic_boundary_image, hboundary, image_comp]
  congr 1
  unfold affineSegment
  apply image_congr
  intro t _
  simp only [affineChartSegment, AffineMap.lineMap_apply_module]
  module




theorem m64Intrinsic_region_circle_side_turning_le
    {I : Type*} (N : IntrinsicAnnulus)
    (face : I → SmoothFace AnnulusCoordinates)
    (F : I → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : I → AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hF : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i) (F i).source)
    (hFi : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i).symm (F i).target)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
    (hboundary : ∀ i k, ((face i).boundary k).map = F i ∘
      affineChartSegment (b i (k.succAbove 0)) (b i (k.succAbove 1)))
    (hinj : ∀ i k, InjOn ((face i).boundary k).map (Icc (0 : ℝ) 1))
    (hinter : ∀ i j, i ≠ j →
      (∃ k l : Fin 3, (face i).carrier ∩ (face j).carrier =
          ((face i).boundary k).map '' Icc (0 : ℝ) 1 ∧
        ((face i).boundary k).map '' Icc (0 : ℝ) 1 =
          ((face j).boundary l).map '' Icc (0 : ℝ) 1) ∨
      ∃ w : Fin 3, (face i).carrier ∩ (face j).carrier ⊆ {F i (b i w)})
    (Q : ∀ i, RiemannianMetric.AlignedChartFrame N.metric (coordinateTriangleChart (F i) (b i)))
    {a b0 : ℝ} (hab : a ≤ b0)
    (hcircleInj : InjOn (intrinsicAnnulusBoundary 1) (Icc a b0))
    (T : Finset (I × Fin 3))
    (hunpaired : ∀ p ∈ T, ∀ q : I × Fin 3,
      faceBoundaryIndex face q.1 q.2 = faceBoundaryIndex face p.1 p.2 → q = p)
    (himage : ∀ p ∈ T, ((face p.1).boundary p.2).map '' Icc (0 : ℝ) 1 ⊆
      intrinsicAnnulusBoundary 1 '' Icc a b0) :
    (∑ p ∈ T, |coordinateTriangleTurningIntegral N.connection (F p.1) (b p.1) (Q p.1)
      (p.2 + 1) ((p.2 + 1) + 1)|) ≤
        intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b0 := by
  classical
  have hex (p : I × Fin 3) : ∃ lo hi : ℝ, p ∈ T →
      a ≤ lo ∧ lo < hi ∧ hi ≤ b0 ∧
      ((face p.1).boundary p.2).map '' Icc (0 : ℝ) 1 =
        intrinsicAnnulusBoundary 1 '' Icc lo hi ∧
      |coordinateTriangleTurningIntegral N.connection (F p.1) (b p.1) (Q p.1)
        (p.2 + 1) ((p.2 + 1) + 1)| ≤
          intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 lo hi := by
    by_cases hp : p ∈ T
    · have hne : p.2 + 1 ≠ (p.2 + 1) + 1 := by
        have h (k : Fin 3) : k + 1 ≠ (k + 1) + 1 := by fin_cases k <;> decide
        exact h p.2
      obtain ⟨lo, hi, hlo, hlt, hhi, hside, hturn⟩ :=
        m64Intrinsic_coordinate_side_boundary_arc_turning_bound N (F p.1) (b p.1)
          (hF p.1) (hFi p.1) (hsource p.1) (Q p.1) hne (by norm_num : (1 : ℝ) ≠ 0)
          hcircleInj (by rw [cyclic_side_image face F b hboundary]; exact himage p hp)
      rw [cyclic_side_image face F b hboundary] at hside
      exact ⟨lo, hi, fun _ => ⟨hlo, hlt, hhi, hside, hturn⟩⟩
    · exact ⟨0, 0, fun hp' => (hp hp').elim⟩
  choose lo hi hdata using hex
  have hsum := (m64Intrinsic_region_boundary_side_intervals_disjoint_turning_le
    N face F b hsource hboundary hinj hinter hab (intrinsicAnnulusBoundary 1)
    (m64Intrinsic_contDiff_boundary 1).continuous.continuousOn hcircleInj T lo hi
    (fun p hp => ⟨(hdata p hp).1, (hdata p hp).2.1, (hdata p hp).2.2.1⟩)
    hunpaired (fun p hp => (hdata p hp).2.2.2.1)).2
  exact (Finset.sum_le_sum fun p hp => (hdata p hp).2.2.2.2).trans hsum

open Classical in



theorem m64Intrinsic_region_circle_geodesic_turning_le
    {I : Type*} [Fintype I] (N : IntrinsicAnnulus)
    (face : I → SmoothFace AnnulusCoordinates)
    (F : I → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : I → AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hF : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i) (F i).source)
    (hFi : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i).symm (F i).target)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
    (hboundary : ∀ i k, ((face i).boundary k).map = F i ∘
      affineChartSegment (b i (k.succAbove 0)) (b i (k.succAbove 1)))
    (hinj : ∀ i k, InjOn ((face i).boundary k).map (Icc (0 : ℝ) 1))
    (hinter : ∀ i j, i ≠ j →
      (∃ k l : Fin 3, (face i).carrier ∩ (face j).carrier =
          ((face i).boundary k).map '' Icc (0 : ℝ) 1 ∧
        ((face i).boundary k).map '' Icc (0 : ℝ) 1 =
          ((face j).boundary l).map '' Icc (0 : ℝ) 1) ∨
      ∃ w : Fin 3, (face i).carrier ∩ (face j).carrier ⊆ {F i (b i w)})
    (Q : ∀ i, RiemannianMetric.AlignedChartFrame N.metric (coordinateTriangleChart (F i) (b i)))
    {a b0 : ℝ} (hab : a ≤ b0)
    (hcircleInj : InjOn (intrinsicAnnulusBoundary 1) (Icc a b0))
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {c d : ℝ}
    (hgeo : N.metric.IsGeodesicOn gamma (Icc c d)) (hgammaInj : InjOn gamma (Icc c d))
    (hunit : ∀ p ∈ Icc c d,
      N.metric.inner (gamma p) (deriv gamma p) (deriv gamma p) = 1)
    (hclass : ∀ p : I × Fin 3,
      (∀ q : I × Fin 3,
        faceBoundaryIndex face q.1 q.2 = faceBoundaryIndex face p.1 p.2 → q = p) →
      ((face p.1).boundary p.2).map '' Icc (0 : ℝ) 1 ⊆
        intrinsicAnnulusBoundary 1 '' Icc a b0 ∨
      ((face p.1).boundary p.2).map '' Icc (0 : ℝ) 1 ⊆ gamma '' Icc c d) :
    (∑ p : I × Fin 3, if ∀ q : I × Fin 3,
        faceBoundaryIndex face q.1 q.2 = faceBoundaryIndex face p.1 p.2 → q = p then
      coordinateTriangleTurningIntegral N.connection (F p.1) (b p.1) (Q p.1)
        (p.2 + 1) ((p.2 + 1) + 1) else 0) ≤
      intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b0 := by
  classical
  let turn (p : I × Fin 3) := coordinateTriangleTurningIntegral N.connection
    (F p.1) (b p.1) (Q p.1) (p.2 + 1) ((p.2 + 1) + 1)
  let unpaired (p : I × Fin 3) := ∀ q : I × Fin 3,
    faceBoundaryIndex face q.1 q.2 = faceBoundaryIndex face p.1 p.2 → q = p
  let onCircle (p : I × Fin 3) := ((face p.1).boundary p.2).map '' Icc (0 : ℝ) 1 ⊆
    intrinsicAnnulusBoundary 1 '' Icc a b0
  let T := Finset.univ.filter (fun p => unpaired p ∧ onCircle p)
  have hbound : (∑ p ∈ T, |turn p|) ≤
      intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b0 :=
    m64Intrinsic_region_circle_side_turning_le N face F b hF hFi hsource hboundary
      hinj hinter Q hab hcircleInj T
      (fun p hp => (Finset.mem_filter.mp hp).2.1)
      (fun p hp => (Finset.mem_filter.mp hp).2.2)
  change (∑ p : I × Fin 3, if unpaired p then turn p else 0) ≤ _
  have hcompare (p : I × Fin 3) : (if unpaired p then turn p else 0) ≤
      if p ∈ T then |turn p| else 0 := by
    by_cases hu : unpaired p
    · by_cases hc : onCircle p
      · have hp : p ∈ T := by
          simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hu, hc⟩
        simpa only [if_pos hu, if_pos hp] using le_abs_self (turn p)
      · have hp : p ∉ T := by
          simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
          exact fun h => hc h.2
        have himage := (hclass p hu).resolve_left hc
        have hzero : turn p = 0 := by
          apply m64Intrinsic_coordinate_side_geodesic_arc_turning_eq_zero N.connection
            (F p.1) (b p.1) (hF p.1) (hFi p.1) (hsource p.1) (Q p.1)
            (by have h (k : Fin 3) : k + 1 ≠ (k + 1) + 1 := by fin_cases k <;> decide
                exact h p.2) hg hgeo hgammaInj hunit
          rw [cyclic_side_image face F b hboundary]
          exact himage
        simp only [if_pos hu, if_neg hp, hzero, le_refl]
    · have hp : p ∉ T := by
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
        exact fun h => hu h.1
      simp only [if_neg hu, if_neg hp, le_refl]
  calc
    _ ≤ ∑ p : I × Fin 3, if p ∈ T then |turn p| else 0 :=
      Finset.sum_le_sum fun p _ => hcompare p
    _ = ∑ p ∈ T, |turn p| := by simp
    _ ≤ _ := hbound

end PoincareConjecture
