import PoincareConjecture.Proofs.M35.RadialGauge.SmoothGaugeIdentity

set_option autoImplicit false

open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem smoothGaugeForcing_eq_norm_radial {h f₀ xi : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (he : Function.Even h) (hzero : h 0 = 0)
    (hf : ContDiff ℝ ∞ f₀) (hfo : Function.Odd f₀)
    (hfzero : f₀ 0 = 0) (hdfzero : deriv f₀ 0 = 1)
    {x : E} (hx : x ≠ 0) (sigma : ℝ) :
    smoothGaugeForcing h f₀ xi x sigma =
      radialGaugeForcing (mapRadius h) f₀ (fun s => s * xi s) sigma ‖x‖ := by
  have heq : smoothGaugeForcing h f₀ xi x sigma =
      smoothGaugeForcing h f₀ xi ‖x‖ sigma := by
    simp only [smoothGaugeForcing, norm_smul, Real.norm_eq_abs, Real.abs_exp,
      abs_norm, smul_eq_mul, abs_mul]
  rw [heq]
  exact smoothGaugeForcing_eq_radial hh he hzero hf hfo hfzero hdfzero
    (norm_pos_iff.mpr hx) sigma

theorem smoothGaugeForcing_eq_exterior_formula {h f₀ xi : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (he : Function.Even h) (hzero : h 0 = 0)
    (hf : ContDiff ℝ ∞ f₀) (hfo : Function.Odd f₀)
    (hfzero : f₀ 0 = 0) (hdfzero : deriv f₀ 0 = 1)
    {x : E} (hx : x ≠ 0) (sigma : ℝ) :
    smoothGaugeForcing h f₀ xi x sigma =
      radialGaugeDrift (mapRadius h) (fun s => s * xi s) ‖x‖ / ‖x‖ +
        2 / ‖x‖ ^ 2 - 2 * smoothTargetCoupling f₀ ‖Real.exp sigma • x‖ *
          (1 / mapRadius h ‖x‖) ^ 2 := by
  rw [smoothGaugeForcing_eq_norm_radial hh he hzero hf hfo hfzero hdfzero hx sigma]
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hq : 0 < ‖Real.exp sigma • x‖ := norm_pos_iff.mpr
    (smul_ne_zero (Real.exp_ne_zero _) hx)
  rw [smoothTargetCoupling_eq_exterior hf hfzero hq.ne', norm_smul,
    Real.norm_eq_abs, Real.abs_exp, mul_comm (Real.exp sigma) ‖x‖]
  unfold radialGaugeForcing cylinderTargetForcing radialGaugeDrift
  have hfr : mapRadius h ‖x‖ ≠ 0 := mul_ne_zero hr.ne' (Real.exp_ne_zero _)
  field_simp [hr.ne', hfr]
  ring

end PoincareConjecture.M35.RadialGauge
