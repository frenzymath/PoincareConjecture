import PoincareConjecture.Proofs.M35.RadialGauge.ExteriorCoefficients

set_option autoImplicit false

open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

noncomputable def radialTargetCoupling (f₀ : ℝ → ℝ) (s : ℝ) : ℝ :=
  f₀ s * deriv f₀ s / s

noncomputable def radialGaugeForcing (f f₀ velocity : ℝ → ℝ) (sigma r : ℝ) : ℝ :=
  cylinderTargetForcing f velocity r -
    2 * radialTargetCoupling f₀ (r * Real.exp sigma) / f r ^ 2

theorem radialGaugeForcing_eq (f f₀ velocity : ℝ → ℝ) (sigma r : ℝ) :
    radialGaugeForcing f f₀ velocity sigma r =
      2 * deriv f r / (r * f r) -
      2 * f₀ (r * Real.exp sigma) * deriv f₀ (r * Real.exp sigma) /
        (r * Real.exp sigma * f r ^ 2) - velocity r / r := by
  unfold radialGaugeForcing cylinderTargetForcing radialTargetCoupling
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem radialTargetCoupling_hasDerivAt {f₀ : ℝ → ℝ}
    (hf₀ : ContDiff ℝ ∞ f₀) {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (radialTargetCoupling f₀)
      ((deriv f₀ s ^ 2 + f₀ s * deriv (deriv f₀) s) / s -
        f₀ s * deriv f₀ s / s ^ 2) s := by
  have hf := (hf₀.differentiable (by simp) s).hasDerivAt
  have hdf := ((contDiff_infty_iff_deriv.mp hf₀).2.differentiable (by simp) s).hasDerivAt
  have h := (hf.mul hdf).div (hasDerivAt_id s) hs
  change HasDerivAt (radialTargetCoupling f₀) _ s at h
  apply h.congr_deriv
  simp only [id_eq, Pi.mul_apply, mul_one]
  field_simp [hs]

theorem radialGaugeForcing_hasDerivAt {f f₀ velocity : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hf₀ : ContDiff ℝ ∞ f₀) (sigma : ℝ)
    {r : ℝ} (hr : r ≠ 0) (hfr : f r ≠ 0)
    (hv : HasDerivAt velocity (2 * deriv (deriv f) r / f r) r) :
    HasDerivAt (radialGaugeForcing f f₀ velocity sigma)
      (-2 * (deriv f r / f r) ^ 2 / r - 2 * (deriv f r / f r) / r ^ 2 +
        velocity r / r ^ 2 -
        2 * deriv (radialTargetCoupling f₀) (r * Real.exp sigma) * Real.exp sigma / f r ^ 2 +
        4 * radialTargetCoupling f₀ (r * Real.exp sigma) * deriv f r / f r ^ 3) r := by
  have hff := (hf.differentiable (by simp) r).hasDerivAt
  have htarget := radialTargetCoupling_hasDerivAt hf₀
    (mul_ne_zero hr (Real.exp_ne_zero sigma))
  have htd : HasDerivAt (radialTargetCoupling f₀)
      (deriv (radialTargetCoupling f₀) (r * Real.exp sigma)) (r * Real.exp sigma) :=
    htarget.differentiableAt.hasDerivAt
  have hcomp := htd.comp r ((hasDerivAt_id r).mul_const (Real.exp sigma))
  have h := (cylinderTargetForcing_hasDerivAt hf hr hfr hv).sub
    ((hcomp.const_mul 2).div (hff.pow 2) (pow_ne_zero 2 hfr))
  change HasDerivAt (radialGaugeForcing f f₀ velocity sigma) _ r at h
  apply h.congr_deriv
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, one_mul, id_eq,
    Function.comp_apply, Pi.pow_apply]
  field_simp [hr, hfr]
  ring

end PoincareConjecture.M35.RadialGauge
