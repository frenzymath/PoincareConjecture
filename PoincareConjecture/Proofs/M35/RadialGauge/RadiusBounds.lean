import PoincareConjecture.Proofs.M35.RadialGauge.RadiusEnd

set_option autoImplicit false

open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

theorem mapRadius_deriv_positive {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u)
    {eta r : ℝ} (heta : eta < 1)
    (hd : (1 + |r|) * |deriv u r| ≤ eta) : 0 < deriv (mapRadius u) r := by
  rw [(mapRadius_hasDerivAt ((hu.differentiable (by simp) r).hasDerivAt)).deriv]
  have hr : |r * deriv u r| ≤ eta := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (by linarith : |r| ≤ 1 + |r|) (abs_nonneg _)).trans hd
  exact mul_pos (Real.exp_pos _) (by linarith only [neg_le_of_abs_le hr, heta])

theorem mapRadius_third_deriv_bound {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u)
    {r eta H J : ℝ} (hr : 0 ≤ r) (heta : 0 ≤ eta)
    (hv : |u r| ≤ eta)
    (hdu : (1 + r) * |deriv u r| ≤ eta)
    (hddu : (1 + r) * |deriv (deriv u) r| ≤ H)
    (hdddu : (1 + r) * |deriv (deriv (deriv u)) r| ≤ J) :
    |deriv (deriv (deriv (mapRadius u))) r| ≤
      Real.exp eta * (3 * eta ^ 2 + 3 * H + eta ^ 3 + 3 * eta * H + J) := by
  let p := deriv u r
  let q := deriv (deriv u) r
  let z := deriv (deriv (deriv u)) r
  have hp : |p| ≤ eta := by
    nlinarith only [hdu, mul_nonneg hr (abs_nonneg p)]
  have hq : |q| ≤ H := by
    nlinarith only [hddu, mul_nonneg hr (abs_nonneg q)]
  have hrp : r * |p| ≤ eta := by nlinarith only [hdu, abs_nonneg p]
  have hrz : r * |z| ≤ J := by nlinarith only [hdddu, abs_nonneg z]
  have hp2 : |p| ^ 2 ≤ eta ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hp 2
  have hp3 : r * |p| ^ 3 ≤ eta ^ 3 := by
    have h := mul_le_mul hrp hp2 (sq_nonneg _) heta
    nlinarith only [h]
  have hpq : r * |p| * |q| ≤ eta * H :=
    mul_le_mul hrp hq (abs_nonneg _) heta
  have hraw : |3 * p ^ 2 + 3 * q + r * (p ^ 3 + 3 * p * q + z)| ≤
      3 * |p| ^ 2 + 3 * |q| + r * (|p| ^ 3 + 3 * |p| * |q| + |z|) := by
    calc
      _ ≤ |3 * p ^ 2| + |3 * q| + |r| * (|p ^ 3| + |3 * p * q| + |z|) := by
        apply (abs_add_le _ _).trans
        apply add_le_add (abs_add_le _ _) _
        rw [abs_mul]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
      _ = _ := by simp [abs_mul, abs_pow, abs_of_nonneg hr]
  have hbound : |3 * p ^ 2 + 3 * q + r * (p ^ 3 + 3 * p * q + z)| ≤
      3 * eta ^ 2 + 3 * H + eta ^ 3 + 3 * eta * H + J := by
    nlinarith only [hraw, hp2, hq, hp3, hpq, hrz]
  rw [mapRadius_third_deriv hu, abs_mul, Real.abs_exp]
  exact mul_le_mul (Real.exp_le_exp.mpr ((le_abs_self _).trans hv)) hbound
    (abs_nonneg _) (Real.exp_nonneg _)

end PoincareConjecture.M35.RadialGauge
