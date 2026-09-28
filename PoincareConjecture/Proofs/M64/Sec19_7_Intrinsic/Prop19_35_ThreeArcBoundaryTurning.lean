import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcSideClassification
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionArcTurning

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

private theorem cyclic_side_image {K : Set AnnulusCoordinates}
    (R : M64IntrinsicCoordinateTriangulation K) (i : Fin R.count) (k : Fin 3) :
    (fun t : ℝ => R.coordinates i
      (AffineMap.lineMap (R.basis i (k + 1)) (R.basis i ((k + 1) + 1)) t)) '' Icc (0 : ℝ) 1 =
      ((R.face i).boundary k).map '' Icc (0 : ℝ) 1 := by
  rw [coordinateTriangle_cyclic_boundary_image, R.boundary, image_comp]
  congr 1
  unfold affineSegment
  apply image_congr
  intro t _
  simp only [affineChartSegment, AffineMap.lineMap_apply_module]
  module

open Classical in

theorem m64Intrinsic_region_circle_two_geodesics_turning_le
    (N : IntrinsicAnnulus) {K : Set AnnulusCoordinates}
    (R : M64IntrinsicCoordinateTriangulation K)
    (Q : ∀ i, RiemannianMetric.AlignedChartFrame N.metric
      (coordinateTriangleChart (R.coordinates i) (R.basis i)))
    {a b : ℝ} (hab : a ≤ b)
    (hcircleInj : InjOn (intrinsicAnnulusBoundary 1) (Icc a b))
    (eta : Bool → ℝ → AnnulusCoordinates) (L : Bool → ℝ)
    (he : ∀ e, ContDiff ℝ ∞ (eta e))
    (hgeo : ∀ e, N.metric.IsGeodesicOn (eta e) (Icc 0 (L e)))
    (hei : ∀ e, InjOn (eta e) (Icc 0 (L e)))
    (hunit : ∀ e, ∀ t ∈ Icc 0 (L e),
      N.metric.inner (eta e t) (deriv (eta e) t) (deriv (eta e) t) = 1)
    (hclass : ∀ p : Fin R.count × Fin 3,
      (∀ q : Fin R.count × Fin 3,
        faceBoundaryIndex R.face q.1 q.2 = faceBoundaryIndex R.face p.1 p.2 → q = p) →
      ((R.face p.1).boundary p.2).map '' Icc (0 : ℝ) 1 ⊆
        intrinsicAnnulusBoundary 1 '' Icc a b ∨
      ∃ e, ((R.face p.1).boundary p.2).map '' Icc (0 : ℝ) 1 ⊆ eta e '' Icc 0 (L e)) :
    (∑ p : Fin R.count × Fin 3, if ∀ q : Fin R.count × Fin 3,
        faceBoundaryIndex R.face q.1 q.2 = faceBoundaryIndex R.face p.1 p.2 → q = p then
      coordinateTriangleTurningIntegral N.connection (R.coordinates p.1) (R.basis p.1)
        (Q p.1) (p.2 + 1) ((p.2 + 1) + 1) else 0) ≤
      intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b := by
  classical
  let turn (p : Fin R.count × Fin 3) := coordinateTriangleTurningIntegral N.connection
    (R.coordinates p.1) (R.basis p.1) (Q p.1) (p.2 + 1) ((p.2 + 1) + 1)
  let unpaired (p : Fin R.count × Fin 3) := ∀ q : Fin R.count × Fin 3,
    faceBoundaryIndex R.face q.1 q.2 = faceBoundaryIndex R.face p.1 p.2 → q = p
  let onCircle (p : Fin R.count × Fin 3) :=
    ((R.face p.1).boundary p.2).map '' Icc (0 : ℝ) 1 ⊆ intrinsicAnnulusBoundary 1 '' Icc a b
  let E := Finset.univ.filter (fun p => unpaired p ∧ onCircle p)
  have hbound : (∑ p ∈ E, |turn p|) ≤
      intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b :=
    m64Intrinsic_region_circle_side_turning_le N R.face R.coordinates R.basis
      R.smooth R.inverse_smooth R.source R.boundary R.boundary_injective R.intersections
      Q hab hcircleInj E (fun p hp => (Finset.mem_filter.mp hp).2.1)
      (fun p hp => (Finset.mem_filter.mp hp).2.2)
  change (∑ p : Fin R.count × Fin 3, if unpaired p then turn p else 0) ≤ _
  have hcompare (p : Fin R.count × Fin 3) : (if unpaired p then turn p else 0) ≤
      if p ∈ E then |turn p| else 0 := by
    by_cases hu : unpaired p
    · by_cases hc : onCircle p
      · have hp : p ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_univ p, hu, hc⟩
        simpa only [if_pos hu, if_pos hp] using le_abs_self (turn p)
      · have hp : p ∉ E := fun hh => hc (Finset.mem_filter.mp hh).2.2
        obtain ⟨e, himage⟩ := (hclass p hu).resolve_left hc
        have hzero : turn p = 0 := by
          apply m64Intrinsic_coordinate_side_geodesic_arc_turning_eq_zero N.connection
            (R.coordinates p.1) (R.basis p.1) (R.smooth p.1) (R.inverse_smooth p.1)
            (R.source p.1) (Q p.1)
            (by have h (k : Fin 3) : k + 1 ≠ (k + 1) + 1 := by fin_cases k <;> decide
                exact h p.2) (he e) (hgeo e) (hei e) (hunit e)
          rw [cyclic_side_image R]
          exact himage
        simp only [if_pos hu, if_neg hp, hzero, le_refl]
    · have hp : p ∉ E := fun hh => hu (Finset.mem_filter.mp hh).2.1
      simp only [if_neg hu, if_neg hp, le_refl]
  calc
    _ ≤ ∑ p : Fin R.count × Fin 3, if p ∈ E then |turn p| else 0 :=
      Finset.sum_le_sum fun p _ => hcompare p
    _ = ∑ p ∈ E, |turn p| := by simp
    _ ≤ _ := hbound

end PoincareConjecture
