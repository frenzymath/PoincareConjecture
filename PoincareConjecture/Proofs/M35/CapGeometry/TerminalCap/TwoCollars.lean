import PoincareConjecture.Proofs.M35.CapGeometry.TerminalCap.BoundaryScale
import PoincareConjecture.Proofs.M35.CapGeometry.RadialAnnulusThreshold
import PoincareConjecture.Proofs.M35.CapGeometry.ScalarRadialNeck









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

open OrdinaryRealization



structure RadialCapCollars {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) (t : ℝ)
    (ht : t ∈ Ico 0 E.flow.base.lifetime) (epsilon : ℝ) where
  q : UnitTwoSphere
  a : ℝ
  b : ℝ
  b' : ℝ
  Q : ℝ
  Q' : ℝ
  a_pos : 0 < a
  b_pos : 0 < b
  b'_pos : 0 < b'
  Q_pos : 0 < Q
  Q'_pos : 0 < Q'
  unit : Q * b ^ 2 = 1
  unit' : Q' * b' ^ 2 = 1
  inner_pos : 0 < a - b * epsilon⁻¹
  boundary_inner_pos : 0 < (a - b * epsilon⁻¹) - b' * epsilon⁻¹
  speed : b' < 2 * b
  scalar : (E.flow.connection t).scalarCurvature
    (intrinsicSpatialInverse (E.flow.metric t) (E.rotation_invariant t ht)
      (E.complete t ht) (a • q.val)) = Q
  boundary_scalar : (E.flow.connection t).scalarCurvature
    (intrinsicSpatialInverse (E.flow.metric t) (E.rotation_invariant t ht)
      (E.complete t ht) ((a - b * epsilon⁻¹) • q.val)) = Q'
  comparison : RoundCylinderClose epsilon 0 (radialCylinderTensor
    (fun u => Q * intrinsicWarpingRadius (E.flow.metric t)
      (E.rotation_invariant t ht) (E.complete t ht) (a + b * u) ^ 2) 1)
  boundary_comparison : RoundCylinderClose epsilon 0 (radialCylinderTensor
    (fun u => Q' * intrinsicWarpingRadius (E.flow.metric t)
      (E.rotation_invariant t ht) (E.complete t ht)
        ((a - b * epsilon⁻¹) + b' * u) ^ 2) 1)
  far : 6 * intrinsicWarpingRadius (E.flow.metric t)
    (E.rotation_invariant t ht) (E.complete t ht) a < a
  width : intrinsicWarpingRadius (E.flow.metric t)
    (E.rotation_invariant t ht) (E.complete t ht) a < 2 * (b * epsilon⁻¹)
  radius : intrinsicWarpingRadius (E.flow.metric t)
    (E.rotation_invariant t ht) (E.complete t ht) a < 2 * b



theorem exists_radial_cap_collars_threshold (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    {epsilon : ℝ} (he : 0 < epsilon) (hehalf : epsilon < 1 / 2) :
    ∃ T : ℝ, 0 < T ∧ ∀ t, ∀ ht : t ∈ Ico 0 E.flow.base.lifetime,
      ∀ y : StandardCapSpace, T ≤ (E.flow.connection t).scalarCurvature y →
        T ≤ ((E.flow.metric t).edist 0 y).toReal *
          Real.sqrt ((E.flow.connection t).scalarCurvature y) →
        ∃ N : RadialCapCollars E t ht epsilon,
          N.a = radialArclength (E.flow.metric t) ‖y‖ ∧
          N.b = (Real.sqrt ((E.flow.connection t).scalarCurvature y))⁻¹ ∧
          N.Q = (E.flow.connection t).scalarCurvature y := by
  obtain ⟨B, hB, hneck⟩ := exists_radial_annulus_comparison_threshold P E epsilon he
  let T := 4 * B + 16 + 4 * epsilon⁻¹
  have hel : 0 < epsilon⁻¹ := inv_pos.mpr he
  have hT : 0 < T := by dsimp only [T]; positivity
  refine ⟨T, hT, ?_⟩
  intro t ht y hhigh hdistance
  let g := E.flow.metric t
  let D := E.flow.connection t
  let hrot := E.rotation_invariant t ht
  let hc := E.complete t ht
  let Q := D.scalarCurvature y
  let b := (Real.sqrt Q)⁻¹
  let a := radialArclength g ‖y‖
  have hQ : 0 < Q := E.scalar_pos ht y
  have hsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hb : 0 < b := inv_pos.mpr hsqrt
  have hunit : Q * b ^ 2 = 1 := by
    dsimp only [b]
    rw [inv_pow, Real.sq_sqrt hQ.le, mul_inv_cancel₀ hQ.ne']
  have ha0 : 0 ≤ a := by
    simpa only [radialArclength_zero] using
      (radialArclength_strictMono g).monotone (norm_nonneg y)
  have hd : T ≤ a * Real.sqrt Q := by
    change T ≤ (g.edist 0 y).toReal * Real.sqrt Q at hdistance
    rw [edist_zero_eq_radialArclength g hrot hc P, ENNReal.toReal_ofReal ha0] at hdistance
    exact hdistance
  have hTa : T * b ≤ a := by
    have h := mul_le_mul_of_nonneg_right hd hb.le
    simpa only [b, mul_assoc, mul_inv_cancel₀ hsqrt.ne', mul_one] using h
  have hBa : B ≤ T := by dsimp only [T]; linarith only [hB, hel]
  have hfirst := hneck t ht y (hBa.trans hhigh) (hBa.trans hdistance)
  have hend := hfirst.original
  change 0 < a - b * epsilon⁻¹ ∧ _ at hend
  have ha : 0 < a := by linarith only [hend.1, mul_pos hb hel]
  have hroom : 4 * b < a - b * epsilon⁻¹ := by
    have hcoef : 4 + epsilon⁻¹ < T := by dsimp only [T]; linarith only [hB, hel]
    have h := (mul_lt_mul_of_pos_right hcoef hb).trans_le hTa
    nlinarith only [h]
  let q : UnitTwoSphere := ⟨EuclideanSpace.single (2 : Fin 3) (1 : ℝ), by simp⟩
  let a' := a - b * epsilon⁻¹
  let y' := intrinsicSpatialInverse g hrot hc (a' • q.val)
  let Q' := D.scalarCurvature y'
  let b' := (Real.sqrt Q')⁻¹
  have hQ' : 0 < Q' := E.scalar_pos ht y'
  have hsqrt' : 0 < Real.sqrt Q' := Real.sqrt_pos.mpr hQ'
  have hb' : 0 < b' := inv_pos.mpr hsqrt'
  have hunit' : Q' * b' ^ 2 = 1 := by
    dsimp only [b']
    rw [inv_pow, Real.sq_sqrt hQ'.le, mul_inv_cancel₀ hQ'.ne']
  have hQQ' : Q < 4 * Q' := radial_boundary_scalar_gt_quarter g hrot hc P D
    (E.nonnegative_sectional t ht) q ha hb hQ he hunit
    (hfirst.radius_bound he hehalf) hroom
  have hspeed : b' < 2 * b := scalar_length_lt_twice hQ' hb hb' hunit hunit' hQQ'
  have hhigh' : B ≤ Q' := by
    have hTQ : T ≤ Q := hhigh
    dsimp only [T] at hTQ
    linarith only [hTQ, hQQ', hel]
  have hradial' : radialArclength g ‖y'‖ = a' :=
    radialArclength_intrinsic_center g hrot hc q hend.1.le
  have hBa' : B * b' < a' := by
    have hcoef : 2 * B + epsilon⁻¹ < T := by
      dsimp only [T]
      linarith only [hB, hel]
    have h := (mul_lt_mul_of_pos_right hcoef hb).trans_le hTa
    have hh := mul_lt_mul_of_pos_left hspeed hB
    dsimp only [a']
    nlinarith only [h, hh]
  have hdistance' : B ≤ (g.edist 0 y').toReal * Real.sqrt Q' := by
    rw [edist_zero_eq_radialArclength g hrot hc P, hradial',
      ENNReal.toReal_ofReal hend.1.le]
    have h := mul_lt_mul_of_pos_right hBa' hsqrt'
    have hid : b' * Real.sqrt Q' = 1 := inv_mul_cancel₀ hsqrt'.ne'
    simpa only [mul_assoc, hid, mul_one] using h.le
  have hsecond := (hneck t ht y' hhigh' hdistance').original
  change 0 < radialArclength g ‖y'‖ - b' * epsilon⁻¹ ∧ _ at hsecond
  rw [hradial'] at hsecond
  let f := intrinsicWarpingRadius g hrot hc a
  have hf : 0 < f := intrinsicWarpingRadius_pos g hrot hc ha
  have hfb : f < 2 * b := by
    have hbound := hfirst.radius_bound he hehalf
    have hsq : f ^ 2 < 4 * b ^ 2 := by
      apply (mul_lt_mul_iff_of_pos_left hQ).mp
      nlinarith only [hbound, hunit]
    nlinarith only [hsq, hf, hb]
  have hfar : 6 * f < a := by
    have hcoef : 12 < T := by dsimp only [T]; linarith only [hB, hel]
    have h := (mul_lt_mul_of_pos_right hcoef hb).trans_le hTa
    linarith only [hfb, h]
  have hwidth : f < 2 * (b * epsilon⁻¹) := by
    have helone : 1 < epsilon⁻¹ := (one_lt_inv₀ he).mpr (by linarith only [hehalf])
    have h := mul_lt_mul_of_pos_left helone (mul_pos (by norm_num : (0 : ℝ) < 2) hb)
    nlinarith only [hfb, h]
  let N : RadialCapCollars E t ht epsilon := {
    q := q
    a := a
    b := b
    b' := b'
    Q := Q
    Q' := Q'
    a_pos := ha
    b_pos := hb
    b'_pos := hb'
    Q_pos := hQ
    Q'_pos := hQ'
    unit := hunit
    unit' := hunit'
    inner_pos := hend.1
    boundary_inner_pos := hsecond.1
    speed := hspeed
    scalar := scalar_intrinsic_radial_center_unscaled g hrot hc P D q y
    boundary_scalar := rfl
    comparison := hend.2
    boundary_comparison := hsecond.2
    far := hfar
    width := hwidth
    radius := hfb
  }
  exact ⟨N, rfl, rfl, rfl⟩

end PoincareConjecture.M35.Uniqueness
