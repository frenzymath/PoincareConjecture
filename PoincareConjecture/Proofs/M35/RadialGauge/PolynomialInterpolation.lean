import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option autoImplicit false

open Set
open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

theorem abs_deriv_le_of_forward_interval
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {x h B M : ℝ}
    (hh : 0 < h) (hM : 0 ≤ M)
    (hvalue : |f (x + h)| + |f x| ≤ B)
    (hsecond : ∀ y ∈ Icc x (x + h), |deriv (deriv f) y| ≤ M) :
    |deriv f x| ≤ B / h + M * h := by
  obtain ⟨z, hz, hdz⟩ := exists_deriv_eq_slope f (a := x) (b := x + h)
    (by linarith only [hh])
    hf.continuous.continuousOn (hf.differentiable (by simp)).differentiableOn
  have hds := (contDiff_infty_iff_deriv.mp hf).2
  have hchange := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := deriv f) (f' := deriv (deriv f)) (a := x) (b := x + h)
    (fun y _ => ((hds.differentiable (by simp) y).hasDerivAt).hasDerivWithinAt)
    (fun y hy => by simpa only [Real.norm_eq_abs] using hsecond y ⟨hy.1, hy.2.le⟩)
    z ⟨hz.1.le, hz.2.le⟩
  rw [Real.norm_eq_abs] at hchange
  have hlength : M * (z - x) ≤ M * h :=
    mul_le_mul_of_nonneg_left (by linarith only [hz.2]) hM
  have hmean : |deriv f z| ≤ B / h := by
    rw [hdz, show x + h - x = h by ring, abs_div, abs_of_pos hh]
    have htriangle : |f (x + h) - f x| ≤ |f (x + h)| + |f x| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (f (x + h)) (-f x)
    exact div_le_div_of_nonneg_right (htriangle.trans hvalue) hh.le
  have htriangle := abs_add_le (deriv f x - deriv f z) (deriv f z)
  rw [sub_add_cancel, abs_sub_comm] at htriangle
  linarith only [htriangle, hchange, hlength, hmean]

theorem polynomial_deriv_bound
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ) {C M : ℝ}
    (hM : 0 ≤ M)
    (hvalue : ∀ r ≥ 0, (1 + r ^ 2) ^ (n + n) * |f r| ≤ C)
    (hsecond : ∀ r ≥ 0, |deriv (deriv f) r| ≤ M) :
    ∀ r ≥ 0, (1 + r ^ 2) ^ n * |deriv f r| ≤ 2 * C + M := by
  intro r hr
  let a := (1 + r ^ 2) ^ n
  let h := 1 / a
  have ha : 0 < a := by dsimp only [a]; positivity
  have hh : 0 < h := one_div_pos.mpr ha
  have hrh : 0 ≤ r + h := add_nonneg hr hh.le
  have hpoly : a ≤ (1 + (r + h) ^ 2) ^ n := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith only [hr, hh, sq_nonneg h]
  have hpoly2 := pow_le_pow_left₀ ha.le hpoly 2
  have hleft : a ^ 2 * |f r| ≤ C := by
    simpa only [a, pow_two, pow_add] using hvalue r hr
  have hright : a ^ 2 * |f (r + h)| ≤ C := by
    apply (mul_le_mul_of_nonneg_right hpoly2 (abs_nonneg _)).trans
    simpa only [pow_two, pow_add] using hvalue (r + h) hrh
  have hleft' : |f r| ≤ C / a ^ 2 := (le_div_iff₀ (sq_pos_of_pos ha)).mpr (by
    simpa only [mul_comm] using hleft)
  have hright' : |f (r + h)| ≤ C / a ^ 2 := (le_div_iff₀ (sq_pos_of_pos ha)).mpr (by
    simpa only [mul_comm] using hright)
  have hvalues : |f (r + h)| + |f r| ≤ 2 * C / a ^ 2 := by
    rw [mul_div_assoc]
    linarith only [hleft', hright']
  have hd := abs_deriv_le_of_forward_interval hf hh hM hvalues
    (fun y hy => hsecond y (hr.trans hy.1))
  have heq : (2 * C / a ^ 2) / h + M * h = (2 * C + M) / a := by
    dsimp only [h]
    field_simp [ha.ne']
  rw [heq] at hd
  have hresult := (le_div_iff₀ ha).mp hd
  simpa only [a, mul_comm] using hresult

end PoincareConjecture.M35.RadialGauge
