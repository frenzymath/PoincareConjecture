import PoincareConjecture.Proofs.M35.RadialGauge.ExteriorBounds
import PoincareConjecture.Proofs.M35.RadialGauge.FullForcingDerivative










set_option autoImplicit false

open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge



theorem radialGaugeForcing_weighted_derivative_bound
    {f f₀ velocity : ℝ → ℝ} (hfs : ContDiff ℝ ∞ f) (hf₀ : ContDiff ℝ ∞ f₀)
    {r sigma c V : ℝ} (hr : 1 ≤ r) (hc : 0 < c) (hf : c ≤ f r)
    (hdf : 0 ≤ deriv f r) (hslope : r * deriv f r ≤ f r) (hv : |velocity r| ≤ V)
    (hvd : HasDerivAt velocity (2 * deriv (deriv f) r / f r) r) :
    (1 + r) * |deriv (radialGaugeForcing f f₀ velocity sigma) r| ≤
      (8 + 2 * V) / r +
      (4 * |(r * Real.exp sigma) * deriv (radialTargetCoupling f₀) (r * Real.exp sigma)| +
        8 * |radialTargetCoupling f₀ (r * Real.exp sigma)|) / c ^ 2 := by
  have hrp : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hfr : 0 < f r := hc.trans_le hf
  let q := r * Real.exp sigma
  let H := radialTargetCoupling f₀ q
  let H' := deriv (radialTargetCoupling f₀) q
  let A := 2 * H' * Real.exp sigma / f r ^ 2
  let B := 4 * H * deriv f r / f r ^ 3
  have hq : 0 < q := mul_pos hrp (Real.exp_pos _)
  have hdiff : deriv (radialGaugeForcing f f₀ velocity sigma) r =
      deriv (cylinderTargetForcing f velocity) r - A + B := by
    rw [(radialGaugeForcing_hasDerivAt hfs hf₀ sigma hrp.ne' hfr.ne' hvd).deriv,
      (cylinderTargetForcing_hasDerivAt hfs hrp.ne' hfr.ne' hvd).deriv]
  have hA : |A| = 2 * |H'| * Real.exp sigma / f r ^ 2 := by
    dsimp only [A]
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      Real.abs_exp, abs_pow, abs_of_pos hfr]
  have hB : |B| = 4 * |H| * deriv f r / f r ^ 3 := by
    dsimp only [B]
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
      abs_of_nonneg hdf, abs_pow, abs_of_pos hfr]
  have hfirst : (1 + r) * |A| ≤ 4 * |q * H'| / f r ^ 2 := by
    rw [hA, abs_mul, abs_of_pos hq]
    have hw := mul_le_mul_of_nonneg_right
      (show 1 + r ≤ 2 * r by linarith only [hr])
      (show 0 ≤ 2 * |H'| * Real.exp sigma by positivity)
    apply (le_div_iff₀ (sq_pos_of_pos hfr)).mpr
    have heq : (1 + r) * (2 * |H'| * Real.exp sigma / f r ^ 2) * f r ^ 2 =
        (1 + r) * (2 * |H'| * Real.exp sigma) := by field_simp [hfr.ne']
    rw [heq]
    dsimp only [q]
    nlinarith only [hw]
  have hsecond : (1 + r) * |B| ≤ 8 * |H| / f r ^ 2 := by
    rw [hB]
    have hw : (1 + r) * deriv f r ≤ 2 * f r := by
      have h := mul_le_mul_of_nonneg_right
        (show 1 + r ≤ 2 * r by linarith only [hr]) hdf
      nlinarith only [h, hslope]
    have hratio : (1 + r) * deriv f r / f r ≤ 2 := (div_le_iff₀ hfr).mpr hw
    have hmul := mul_le_mul_of_nonneg_left hratio
      (show 0 ≤ 4 * |H| / f r ^ 2 by positivity)
    convert! hmul using 1 <;> field_simp [hfr.ne']
    ring
  have htriangle : |deriv (cylinderTargetForcing f velocity) r - A + B| ≤
      |deriv (cylinderTargetForcing f velocity) r| + |A| + |B| := by
    apply (abs_add_le _ _).trans
    apply add_le_add _ (le_refl _)
    simpa only [sub_eq_add_neg, abs_neg] using
      abs_add_le (deriv (cylinderTargetForcing f velocity) r) (-A)
  have hweighted := mul_le_mul_of_nonneg_left htriangle
    (show 0 ≤ 1 + r by positivity)
  have hcurrent := cylinderTargetForcing_weighted_derivative_bound hfs hr hfr hdf hslope hv hvd
  have hdenom : (4 * |q * H'| + 8 * |H|) / f r ^ 2 ≤
      (4 * |q * H'| + 8 * |H|) / c ^ 2 := by
    apply div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hc)
    exact pow_le_pow_left₀ hc.le hf 2
  rw [hdiff]
  apply le_trans _ (add_le_add (le_refl ((8 + 2 * V) / r)) hdenom)
  have hsum : 4 * |q * H'| / f r ^ 2 + 8 * |H| / f r ^ 2 =
      (4 * |q * H'| + 8 * |H|) / f r ^ 2 := by ring
  rw [← hsum]
  nlinarith only [hweighted, hcurrent, hfirst, hsecond]

end PoincareConjecture.M35.RadialGauge
