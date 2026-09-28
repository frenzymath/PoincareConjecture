import PoincareConjecture.Proofs.M35.RadialGauge.SmoothGaugeCoefficients










set_option autoImplicit false

open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

open SmoothRadial



theorem smoothGaugeForcing_eq_radial {h f₀ xi : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (he : Function.Even h) (hzero : h 0 = 0)
    (hf : ContDiff ℝ ∞ f₀) (hfo : Function.Odd f₀)
    (hfzero : f₀ 0 = 0) (hdfzero : deriv f₀ 0 = 1)
    {r : ℝ} (hr : 0 < r) (sigma : ℝ) :
    smoothGaugeForcing h f₀ xi r sigma =
      radialGaugeForcing (mapRadius h) f₀ (fun s => s * xi s) sigma r := by
  have hD : axisDivision (deriv h) r = deriv h r / r := by
    apply (eq_div_iff hr.ne').mpr
    simpa only [mul_comm] using mul_axisDivision_deriv hh he r
  have hExp : ContDiff ℝ ∞ (fun s => Real.exp (-2 * h s)) :=
    (contDiff_const.mul hh).exp
  have hExpe : Function.Even (fun s => Real.exp (-2 * h s)) :=
    fun s => congrArg (fun z => Real.exp (-2 * z)) (he s)
  have hE : smoothEvenQuadratic (fun s => Real.exp (-2 * h s)) r =
      (Real.exp (-2 * h r) - 1) / r ^ 2 := by
    have h := smoothEvenQuadratic_identity hExp hExpe r
    rw [hzero, mul_zero, Real.exp_zero] at h
    exact (eq_div_iff (pow_ne_zero 2 hr.ne')).mpr (by simpa only [mul_comm] using h)
  have hq : r * Real.exp sigma ≠ 0 := mul_ne_zero hr.ne' (Real.exp_ne_zero _)
  have hQ : targetQuadraticRemainder f₀ (r * Real.exp sigma) =
      (radialTargetCoupling f₀ (r * Real.exp sigma) - 1) / (r * Real.exp sigma) ^ 2 := by
    have h := targetQuadraticRemainder_identity hf hfo hfzero hdfzero (r * Real.exp sigma)
    rw [smoothTargetCoupling_eq_exterior hf hfzero hq] at h
    exact (eq_div_iff (pow_ne_zero 2 hq)).mpr (by simpa only [mul_comm] using h)
  have hexp (s : ℝ) : Real.exp (2 * s) = Real.exp s ^ 2 := by
    simpa only [Nat.cast_ofNat] using Real.exp_nat_mul s 2
  have hinv : Real.exp (-2 * h r) = (Real.exp (h r) ^ 2)⁻¹ := by
    rw [show -2 * h r = -(2 * h r) by ring, Real.exp_neg, hexp]
  unfold smoothGaugeForcing radialGaugeForcing cylinderTargetForcing
  simp only [Real.norm_eq_abs, smul_eq_mul, abs_mul, Real.abs_exp, abs_of_pos hr]
  rw [mul_comm (Real.exp sigma) r, hD, hE, hQ,
    (mapRadius_hasDerivAt ((hh.differentiable (by simp) r).hasDerivAt)).deriv]
  simp only [mapRadius]
  rw [hexp sigma, hinv]
  field_simp [hr.ne', Real.exp_ne_zero]
  ring



theorem smoothGaugeDrift_eq_radial {h xi : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (he : Function.Even h) {r : ℝ} (hr : 0 < r) :
    smoothGaugeDrift h xi r = radialGaugeDrift (mapRadius h) (fun s => s * xi s) r := by
  have hD : axisDivision (deriv h) r = deriv h r / r := by
    apply (eq_div_iff hr.ne').mpr
    simpa only [mul_comm] using mul_axisDivision_deriv hh he r
  unfold smoothGaugeDrift radialGaugeDrift
  rw [Real.norm_eq_abs, abs_of_pos hr,
    (mapRadius_hasDerivAt ((hh.differentiable (by simp) r).hasDerivAt)).deriv, hD]
  simp only [mapRadius, smul_eq_mul]
  field_simp [hr.ne', Real.exp_ne_zero]
  ring

end PoincareConjecture.M35.RadialGauge
