import PoincareConjecture.Proofs.M35.RadialGauge.FullForcingBounds










set_option autoImplicit false

open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge



theorem radialGaugeForcing_weighted_value_bound
    {f f₀ velocity : ℝ → ℝ} {r c V C : ℝ}
    (hr : 1 ≤ r) (hc : 0 < c) (hf : c ≤ f r)
    (hdf : 0 ≤ deriv f r) (hslope : r * deriv f r ≤ f r)
    (hv : |velocity r| ≤ V) (hH : (1 + r) * |radialTargetCoupling f₀ r| ≤ C) :
    (1 + r) * |radialGaugeForcing f f₀ velocity 0 r| ≤ 4 + 2 * V + 2 * C / c ^ 2 := by
  have hfr : 0 < f r := hc.trans_le hf
  have hC : 0 ≤ C := (mul_nonneg (by positivity) (abs_nonneg _)).trans hH
  have htriangle : |radialGaugeForcing f f₀ velocity 0 r| ≤
      |cylinderTargetForcing f velocity r| + 2 * |radialTargetCoupling f₀ r| / f r ^ 2 := by
    have h := norm_sub_le (cylinderTargetForcing f velocity r)
      (2 * radialTargetCoupling f₀ r / f r ^ 2)
    simpa only [radialGaugeForcing, Real.exp_zero, mul_one, Real.norm_eq_abs,
      abs_div, abs_mul, abs_pow, abs_of_pos hfr,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using h
  have hweighted := mul_le_mul_of_nonneg_left htriangle
    (show 0 ≤ 1 + r by positivity)
  have hcurrent := cylinderTargetForcing_weighted_bound hr hfr hdf hslope hv
  have htarget : (1 + r) * (2 * |radialTargetCoupling f₀ r| / f r ^ 2) ≤
      2 * C / c ^ 2 := by
    calc
      _ = 2 * ((1 + r) * |radialTargetCoupling f₀ r|) / f r ^ 2 := by ring
      _ ≤ 2 * C / f r ^ 2 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hH (by norm_num)) (sq_nonneg _)
      _ ≤ 2 * C / c ^ 2 := div_le_div_of_nonneg_left (by positivity)
        (sq_pos_of_pos hc) (pow_le_pow_left₀ hc.le hf 2)
  nlinarith only [hweighted, hcurrent, htarget]



theorem radialGaugeForcing_weighted_derivative_inverse_radius
    {f f₀ velocity : ℝ → ℝ} (hfs : ContDiff ℝ ∞ f) (hf₀ : ContDiff ℝ ∞ f₀)
    {r sigma eta c V C₀ C₁ : ℝ} (hr : 1 ≤ r) (hrstrip : Real.exp eta ≤ r)
    (hsigma : |sigma| ≤ eta) (hc : 0 < c) (hf : c ≤ f r)
    (hdf : 0 ≤ deriv f r) (hslope : r * deriv f r ≤ f r) (hv : |velocity r| ≤ V)
    (hvd : HasDerivAt velocity (2 * deriv (deriv f) r / f r) r)
    (hH₀ : (1 + r * Real.exp sigma) *
      |radialTargetCoupling f₀ (r * Real.exp sigma)| ≤ C₀)
    (hH₁ : (1 + r * Real.exp sigma) ^ 2 *
      |deriv (radialTargetCoupling f₀) (r * Real.exp sigma)| ≤ C₁) :
    (1 + r) * |deriv (radialGaugeForcing f f₀ velocity sigma) r| ≤
      (8 + 2 * V + Real.exp eta * (4 * C₁ + 8 * C₀) / c ^ 2) / r := by
  let q := r * Real.exp sigma
  let D := 4 * C₁ + 8 * C₀
  let Z := 4 * |q * deriv (radialTargetCoupling f₀) q| +
    8 * |radialTargetCoupling f₀ q|
  have hrp : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hq : 0 < q := mul_pos hrp (Real.exp_pos _)
  have hexp : 1 ≤ Real.exp eta * Real.exp sigma := by
    rw [← Real.exp_add, Real.one_le_exp_iff]
    linarith only [neg_le_of_abs_le hsigma]
  have hqone : 1 ≤ q := hexp.trans
    (mul_le_mul_of_nonneg_right hrstrip (Real.exp_pos sigma).le)
  have hrq : r ≤ Real.exp eta * q := by
    have h := mul_le_mul_of_nonneg_left hexp hrp.le
    dsimp only [q]
    nlinarith only [h]
  have h0 : q * |radialTargetCoupling f₀ q| ≤ C₀ := by
    have h := mul_le_mul_of_nonneg_right (show q ≤ 1 + q by linarith)
      (abs_nonneg (radialTargetCoupling f₀ q))
    exact h.trans hH₀
  have h1 : q ^ 2 * |deriv (radialTargetCoupling f₀) q| ≤ C₁ := by
    have h := mul_le_mul_of_nonneg_right
      (show q ^ 2 ≤ (1 + q) ^ 2 by nlinarith only [hqone])
      (abs_nonneg (deriv (radialTargetCoupling f₀) q))
    exact h.trans hH₁
  have hqZ : q * Z ≤ D := by
    dsimp only [Z, D]
    rw [abs_mul, abs_of_pos hq]
    nlinarith only [h0, h1]
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  have hrZ : r * Z ≤ Real.exp eta * D := by
    have h := mul_le_mul_of_nonneg_right hrq hZ
    have h' := mul_le_mul_of_nonneg_left hqZ (Real.exp_pos eta).le
    nlinarith only [h, h']
  have hdenom : (Z / c ^ 2) * r ≤ Real.exp eta * D / c ^ 2 := by
    rw [div_mul_eq_mul_div₀, mul_comm Z r]
    exact div_le_div_of_nonneg_right hrZ (sq_nonneg c)
  have hmain := radialGaugeForcing_weighted_derivative_bound hfs hf₀
    (sigma := sigma) hr hc hf hdf hslope hv hvd
  change (1 + r) * |deriv (radialGaugeForcing f f₀ velocity sigma) r| ≤
    (8 + 2 * V) / r + Z / c ^ 2 at hmain
  apply (le_div_iff₀ hrp).mpr
  have hm := mul_le_mul_of_nonneg_right hmain hrp.le
  have heq : ((8 + 2 * V) / r + Z / c ^ 2) * r =
      (8 + 2 * V) + (Z / c ^ 2) * r := by
    rw [add_mul, div_mul_cancel₀ _ hrp.ne']
  rw [heq] at hm
  exact hm.trans (add_le_add (le_refl _) hdenom)

end PoincareConjecture.M35.RadialGauge
