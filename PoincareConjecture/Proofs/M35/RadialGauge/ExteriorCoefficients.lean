import PoincareConjecture.Proofs.M35.RadialGauge.CorrectedEquation











set_option autoImplicit false

open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge


noncomputable def radialGaugeDrift (f velocity : ℝ → ℝ) (r : ℝ) : ℝ :=
  2 * deriv f r / f r - 2 / r - velocity r


noncomputable def cylinderTargetForcing (f velocity : ℝ → ℝ) (r : ℝ) : ℝ :=
  2 * deriv f r / (r * f r) - velocity r / r



theorem radialGaugeDrift_hasDerivAt {f velocity : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) {r : ℝ} (hr : r ≠ 0) (hfr : f r ≠ 0)
    (hv : HasDerivAt velocity (2 * deriv (deriv f) r / f r) r) :
    HasDerivAt (radialGaugeDrift f velocity)
      (-2 * (deriv f r / f r) ^ 2 + 2 / r ^ 2) r := by
  have hdf := ((contDiff_infty_iff_deriv.mp hf).2.differentiable (by simp) r).hasDerivAt
  have hff := (hf.differentiable (by simp) r).hasDerivAt
  have h := (((hdf.const_mul 2).div hff hfr).sub
    ((hasDerivAt_const r (2 : ℝ)).div (hasDerivAt_id r) hr)).sub hv
  change HasDerivAt (radialGaugeDrift f velocity) _ r at h
  apply h.congr_deriv
  simp only [id_eq]
  field_simp [hr, hfr]
  ring



theorem cylinderTargetForcing_hasDerivAt {f velocity : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) {r : ℝ} (hr : r ≠ 0) (hfr : f r ≠ 0)
    (hv : HasDerivAt velocity (2 * deriv (deriv f) r / f r) r) :
    HasDerivAt (cylinderTargetForcing f velocity)
      (-2 * (deriv f r / f r) ^ 2 / r - 2 * (deriv f r / f r) / r ^ 2 +
        velocity r / r ^ 2) r := by
  have hdf := ((contDiff_infty_iff_deriv.mp hf).2.differentiable (by simp) r).hasDerivAt
  have hff := (hf.differentiable (by simp) r).hasDerivAt
  have h := ((hdf.const_mul 2).div ((hasDerivAt_id r).mul hff)
    (mul_ne_zero hr hfr)).sub (hv.div (hasDerivAt_id r) hr)
  change HasDerivAt (cylinderTargetForcing f velocity) _ r at h
  apply h.congr_deriv
  simp only [id_eq, Pi.mul_apply]
  field_simp [hr, hfr]
  ring



theorem corrected_forcing_eq_cylinderTargetForcing
    (f f₀ velocity u : ℝ → ℝ) (r : ℝ)
    (htarget : deriv f₀ (mapRadius u r) = 0) :
    2 * deriv f r / (r * f r) -
      2 * f₀ (mapRadius u r) * deriv f₀ (mapRadius u r) /
        (mapRadius u r * f r ^ 2) - velocity r / r =
      cylinderTargetForcing f velocity r := by
  simp only [htarget, mul_zero, zero_div, sub_zero, cylinderTargetForcing]

end PoincareConjecture.M35.RadialGauge
