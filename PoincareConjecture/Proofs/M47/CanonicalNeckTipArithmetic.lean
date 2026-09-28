import Mathlib.Analysis.SpecialFunctions.Pow.Real









set_option autoImplicit false

namespace PoincareConjecture.Proofs.M47



theorem cap_tip_distance_bound
    {epsilon D Acap Q h a dBirth dModel Rmodel : ℝ}
    (he : 0 < epsilon)
    (hD : 0 < D) (hAcap : 0 < Acap) (hQ : 0 < Q) (hh : 0 < h) (ha : 0 < a)
    (hnormal : Q * a ^ 2 = 1) (hscale : Q * h ^ 2 ≤ 8 * D)
    (hsetup : epsilon * Real.sqrt D * Acap ≤ 1)
    (hbirthNonneg : 0 ≤ dBirth) (_hmodelNonneg : 0 ≤ dModel)
    (hbirth : dBirth ≤ Acap * h + (5 / 2 : ℝ) * epsilon⁻¹ * a)
    (hmodel : dModel ≤ (101 / 100 : ℝ) * h⁻¹ * dBirth)
    (hscalar : Rmodel ≤ (101 / 100 : ℝ) * Q * h ^ 2) :
    dModel * Real.sqrt Rmodel < (57 / 10 : ℝ) * epsilon⁻¹ := by
  have hQa : Real.sqrt Q * a = 1 := by
    have hsq : (Real.sqrt Q * a) ^ 2 = 1 := by
      rw [mul_pow, Real.sq_sqrt hQ.le]
      exact hnormal
    nlinarith only [hsq, mul_pos (Real.sqrt_pos.mpr hQ) ha]
  have hQh : Real.sqrt Q * h ≤ 3 * Real.sqrt D := by
    have hsq : (Real.sqrt Q * h) ^ 2 ≤ 8 * D := by
      rw [mul_pow, Real.sq_sqrt hQ.le]
      exact hscale
    nlinarith only [hsq, Real.sq_sqrt hD.le, Real.sqrt_nonneg D,
      mul_pos (Real.sqrt_pos.mpr hQ) hh]
  have hR : Real.sqrt Rmodel ≤ (101 / 100 : ℝ) * Real.sqrt Q * h := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hpositive : 0 ≤ Q * h ^ 2 := mul_nonneg hQ.le (sq_nonneg h)
    have hsq : ((101 / 100 : ℝ) * Real.sqrt Q * h) ^ 2 =
        (101 / 100 : ℝ) ^ 2 * Q * h ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hQ.le]
    rw [hsq]
    nlinarith only [hscalar, hpositive]
  have hcap : Real.sqrt D * Acap ≤ epsilon⁻¹ := by
    have h := (le_inv_mul_iff₀ he).mpr
      (show epsilon * (Real.sqrt D * Acap) ≤ 1 by nlinarith only [hsetup])
    simpa only [mul_one] using h
  have hcapQ := mul_le_mul_of_nonneg_right hQh hAcap.le
  have hcapBound : Real.sqrt Q * Acap * h ≤ 3 * epsilon⁻¹ := by
    nlinarith only [hcapQ, hcap]
  have hbirthQ := mul_le_mul_of_nonneg_left hbirth (Real.sqrt_nonneg Q)
  have hdistQ : Real.sqrt Q * dBirth ≤ (11 / 2 : ℝ) * epsilon⁻¹ := by
    have hcancel : Real.sqrt Q * (Acap * h + (5 / 2 : ℝ) * epsilon⁻¹ * a) =
        Real.sqrt Q * Acap * h + (5 / 2 : ℝ) * epsilon⁻¹ := by
      calc
        _ = Real.sqrt Q * Acap * h +
            (5 / 2 : ℝ) * epsilon⁻¹ * (Real.sqrt Q * a) := by ring
        _ = _ := by rw [hQa, mul_one]
    rw [hcancel] at hbirthQ
    linarith only [hbirthQ, hcapBound]
  have hproduct := mul_le_mul hmodel hR (Real.sqrt_nonneg Rmodel)
    (by positivity : 0 ≤ (101 / 100 : ℝ) * h⁻¹ * dBirth)
  have hcancel : ((101 / 100 : ℝ) * h⁻¹ * dBirth) *
      ((101 / 100 : ℝ) * Real.sqrt Q * h) =
        (101 / 100 : ℝ) ^ 2 * (Real.sqrt Q * dBirth) := by
    field_simp
  rw [hcancel] at hproduct
  have h := mul_le_mul_of_nonneg_left hdistQ
    (by norm_num : 0 ≤ (101 / 100 : ℝ) ^ 2)
  nlinarith only [hproduct, h, inv_pos.mpr he]



theorem cap_tip_distance_margin
    {epsilon beta D Acap Q h a dBirth dModel Rmodel : ℝ}
    (he : 0 < epsilon) (hbeta : 0 < beta) (hbetaSmall : beta < 1 / 2)
    (hD : 0 < D) (hAcap : 0 < Acap) (hQ : 0 < Q) (hh : 0 < h) (ha : 0 < a)
    (hnormal : Q * a ^ 2 = 1) (hscale : Q * h ^ 2 ≤ 8 * D)
    (hsetup : epsilon * Real.sqrt D * Acap ≤ 1)
    (hbirthNonneg : 0 ≤ dBirth) (_hmodelNonneg : 0 ≤ dModel)
    (hbirth : dBirth ≤ Acap * h + (5 / 2 : ℝ) * epsilon⁻¹ * a)
    (hmodel : dModel ≤ (101 / 100 : ℝ) * h⁻¹ * dBirth)
    (hscalar : Rmodel ≤ (101 / 100 : ℝ) * Q * h ^ 2) :
    dModel * Real.sqrt Rmodel < (19 / 20 : ℝ) * (beta * epsilon / 3)⁻¹ := by
  have hdist := cap_tip_distance_bound he hD hAcap hQ hh ha hnormal hscale
    hsetup hbirthNonneg _hmodelNonneg hbirth hmodel hscalar
  have hbetaInv : 2 < beta⁻¹ := by
    have h := mul_lt_mul_of_pos_right
      (show 2 * beta < 1 by linarith only [hbetaSmall]) (inv_pos.mpr hbeta)
    simpa only [mul_assoc, mul_inv_cancel₀ hbeta.ne', mul_one, one_mul] using h
  have hmargin : (57 / 10 : ℝ) * epsilon⁻¹ <
      (19 / 20 : ℝ) * (beta * epsilon / 3)⁻¹ := by
    have h := mul_lt_mul_of_pos_right hbetaInv (inv_pos.mpr he)
    have hid : (beta * epsilon / 3)⁻¹ = 3 * beta⁻¹ * epsilon⁻¹ := by
      field_simp
    rw [hid]
    nlinarith only [h]
  exact hdist.trans hmargin

end PoincareConjecture.Proofs.M47
