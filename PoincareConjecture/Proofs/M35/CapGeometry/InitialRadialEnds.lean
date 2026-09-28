import PoincareConjecture.Proofs.M35.CapGeometry.InitialRadialComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

theorem exists_initial_radial_cap_ends
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) {theta epsilon : ℝ}
    (htheta : 0 < theta) (hthetalt : theta < E.flow.base.lifetime)
    (he : 0 < epsilon) (hehalf : epsilon < 1 / 2) :
    ∃ R : ℝ, 0 < R ∧ ∀ t ∈ Icc 0 theta, ∀ a ≥ R,
      let Q := (E.flow.connection t).scalarCurvature
        (rawInverseRadius P E.flow.base E.rotation_invariant t a •
          EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
      let b := (Real.sqrt Q)⁻¹
      let a' := a - b * epsilon⁻¹
      let Q' := (E.flow.connection t).scalarCurvature
        (rawInverseRadius P E.flow.base E.rotation_invariant t a' •
          EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
      let b' := (Real.sqrt Q')⁻¹
      InitialRadialComparison P E t a epsilon ∧
      InitialRadialComparison P E t a' epsilon ∧
      b < 2 ∧ b' < 2 * b ∧
      6 * rawWarpingRadius P E.flow.base E.rotation_invariant t a < a ∧
      rawWarpingRadius P E.flow.base E.rotation_invariant t a < 2 * (b * epsilon⁻¹) := by
  have htone : theta < 1 := E.lifetime_one ▸ hthetalt
  obtain ⟨Rn, hRn, hneck⟩ := exists_initial_radial_comparison_threshold
    P E htheta hthetalt he
  obtain ⟨Rs, hRs, hscalar⟩ := exists_initial_intrinsic_scalar_control
    P E ⟨htheta.le, hthetalt⟩ (by norm_num : (0 : ℝ) < 1 / 4)
  obtain ⟨Rf, hRf, hradius⟩ := exists_initial_intrinsic_squared_radius_control
    P E htheta hthetalt (half_pos (sub_pos.mpr htone))
  let F := 2 * E.initial_estimate.scalar_constant + 1
  have hF : 0 < F := by
    dsimp only [F]
    linarith only [E.initial_estimate.scalar_constant_pos]
  have hel : 0 < epsilon⁻¹ := inv_pos.mpr he
  have helone : 1 < epsilon⁻¹ := (one_lt_inv₀ he).mpr (by linarith only [hehalf])
  let R := Rn + Rs + Rf + 2 * epsilon⁻¹ + 6 * F + 1
  have hR : 0 < R := by dsimp only [R]; positivity
  refine ⟨R, hR, ?_⟩
  intro t ht a ha
  let Q := (E.flow.connection t).scalarCurvature
    (rawInverseRadius P E.flow.base E.rotation_invariant t a •
      EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
  let b := (Real.sqrt Q)⁻¹
  let a' := a - b * epsilon⁻¹
  let Q' := (E.flow.connection t).scalarCurvature
    (rawInverseRadius P E.flow.base E.rotation_invariant t a' •
      EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
  let b' := (Real.sqrt Q')⁻¹
  let f := rawWarpingRadius P E.flow.base E.rotation_invariant t a
  change InitialRadialComparison P E t a epsilon ∧
    InitialRadialComparison P E t a' epsilon ∧ b < 2 ∧ b' < 2 * b ∧
    6 * f < a ∧ f < 2 * (b * epsilon⁻¹)
  have htime : t ∈ Ico 0 E.flow.base.lifetime := ⟨ht.1, ht.2.trans_lt hthetalt⟩
  have haRn : Rn ≤ a := by dsimp only [R] at ha; linarith only [ha, hRs, hRf, hel, hF]
  have haRs : Rs ≤ a := by dsimp only [R] at ha; linarith only [ha, hRn, hRf, hel, hF]
  have haRf : Rf ≤ a := by dsimp only [R] at ha; linarith only [ha, hRn, hRs, hel, hF]
  have hapos : 0 < a := hRn.trans_le haRn
  have hQ : 0 < Q := E.scalar_pos htime _
  have hb : 0 < b := inv_pos.mpr (Real.sqrt_pos.mpr hQ)
  have hunit : Q * b ^ 2 = 1 := by
    dsimp only [b]
    rw [inv_pow, Real.sq_sqrt hQ.le, mul_inv_cancel₀ hQ.ne']
  have hs := hscalar t ht a haRs
  change |(1 - t) * Q - 1| < 1 / 4 at hs
  have hslo := (abs_lt.mp hs).1
  have hshi := (abs_lt.mp hs).2
  have htimeone : 0 < 1 - t := sub_pos.mpr (ht.2.trans_lt htone)
  have hQlo : (1 / 4 : ℝ) < Q := by
    have hmul : (1 - t) * Q ≤ Q := by nlinarith only [ht.1, hQ]
    linarith only [hmul, hslo]
  have hbsmall : b < 2 := by
    have h := mul_lt_mul_of_pos_right hQlo (sq_pos_of_pos hb)
    rw [hunit] at h
    nlinarith only [h, hb]
  have hwsmall : b * epsilon⁻¹ < 2 * epsilon⁻¹ :=
    mul_lt_mul_of_pos_right hbsmall hel
  have ha'Rn : Rn ≤ a' := by
    dsimp only [a']
    dsimp only [R] at ha
    linarith only [ha, hwsmall, hRs, hRf, hF]
  have ha'Rs : Rs ≤ a' := by
    dsimp only [a']
    dsimp only [R] at ha
    linarith only [ha, hwsmall, hRn, hRf, hF]
  have hQ' : 0 < Q' := E.scalar_pos htime _
  have hb' : 0 < b' := inv_pos.mpr (Real.sqrt_pos.mpr hQ')
  have hunit' : Q' * b' ^ 2 = 1 := by
    dsimp only [b']
    rw [inv_pow, Real.sq_sqrt hQ'.le, mul_inv_cancel₀ hQ'.ne']
  have hs' := hscalar t ht a' ha'Rs
  change |(1 - t) * Q' - 1| < 1 / 4 at hs'
  have hs'lo := (abs_lt.mp hs').1
  have hQQ' : Q < 4 * Q' := by
    apply (mul_lt_mul_iff_of_pos_left htimeone).mp
    nlinarith only [hshi, hs'lo]
  have hspeed : b' < 2 * b := by
    have h := mul_lt_mul_of_pos_right hQQ' (sq_pos_of_pos hb)
    rw [hunit] at h
    have hsq : b' ^ 2 < 4 * b ^ 2 := by
      apply (mul_lt_mul_iff_of_pos_left hQ').mp
      nlinarith only [h, hunit']
    nlinarith only [hsq, hb', hb]
  have hcontrols := raw_intrinsic_warping_controls P E.initial_estimate E.flow.base
    htime (E.rotation_invariant t htime) a hapos
  have hfpos : 0 < f := by
    simpa only [f, rawWarpingRadius_eq P E.flow.base E.rotation_invariant htime] using
      hcontrols.1
  have hfbound : f ≤ F := by
    have hfsq : f ^ 2 ≤ 2 * E.initial_estimate.scalar_constant := by
      simpa only [f, rawWarpingRadius_eq P E.flow.base E.rotation_invariant htime] using
        hcontrols.2.1
    dsimp only [F]
    nlinarith only [hfsq, sq_nonneg (f - 1)]
  have hfar : 6 * f < a := by
    dsimp only [R] at ha
    linarith only [ha, hfbound, hRn, hRs, hRf, hel]
  have hfmodel := hradius t ht a haRf
  change |f ^ 2 - 2 * (1 - t)| < (1 - theta) / 2 at hfmodel
  have hfsq : f ^ 2 < (5 / 2) * (1 - t) := by
    have h := (abs_lt.mp hfmodel).2
    linarith only [h, ht.2]
  have hQf : Q * f ^ 2 < 4 := by
    have h := mul_lt_mul_of_pos_left hfsq hQ
    nlinarith only [h, hshi]
  have hfb : f < 2 * b := by
    have hsq : f ^ 2 < 4 * b ^ 2 := by
      apply (mul_lt_mul_iff_of_pos_left hQ).mp
      nlinarith only [hQf, hunit]
    nlinarith only [hsq, hfpos, hb]
  have hwidth : f < 2 * (b * epsilon⁻¹) := by
    have h := mul_lt_mul_of_pos_left helone (mul_pos (by norm_num : (0 : ℝ) < 2) hb)
    nlinarith only [hfb, h]
  exact ⟨hneck t ht a haRn, hneck t ht a' ha'Rn, hbsmall, hspeed, hfar, hwidth⟩

end PoincareConjecture.M35.Uniqueness
