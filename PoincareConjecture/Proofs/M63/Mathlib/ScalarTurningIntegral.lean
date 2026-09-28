import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus











set_option autoImplicit false

open Set MeasureTheory
open scoped ContDiff intervalIntegral

namespace intervalIntegral



theorem integral_abs_deriv_eq_sub_of_monotoneOn {h : ℝ → ℝ} {a b : ℝ}
    (hh : ContDiff ℝ 1 h) (hab : a < b) (hmono : MonotoneOn h (Icc a b)) :
    (∫ x in a..b, |deriv h x|) = h b - h a := by
  have hdiff : Differentiable ℝ h := hh.differentiable (by simp)
  have hsign (x : ℝ) (hx : x ∈ Icc a b) : 0 ≤ deriv h x := by
    rw [← (hdiff x).derivWithin (uniqueDiffOn_Icc hab x hx)]
    exact hmono.derivWithin_nonneg
  calc
    (∫ x in a..b, |deriv h x|) = ∫ x in a..b, deriv h x := by
      apply integral_congr
      intro x hx
      rw [uIcc_of_le hab.le] at hx
      exact abs_of_nonneg (hsign x hx)
    _ = h b - h a := integral_deriv_eq_sub (fun x _ => hdiff x)
      (hh.continuous_deriv_one.intervalIntegrable a b)



theorem integral_abs_deriv_eq_sub_of_antitoneOn {h : ℝ → ℝ} {a b : ℝ}
    (hh : ContDiff ℝ 1 h) (hab : a < b) (hanti : AntitoneOn h (Icc a b)) :
    (∫ x in a..b, |deriv h x|) = h a - h b := by
  have hdiff : Differentiable ℝ h := hh.differentiable (by simp)
  have hsign (x : ℝ) (hx : x ∈ Icc a b) : deriv h x ≤ 0 := by
    rw [← (hdiff x).derivWithin (uniqueDiffOn_Icc hab x hx)]
    exact hanti.derivWithin_nonpos
  calc
    (∫ x in a..b, |deriv h x|) = ∫ x in a..b, -(deriv h x) := by
      apply integral_congr
      intro x hx
      rw [uIcc_of_le hab.le] at hx
      exact abs_of_nonpos (hsign x hx)
    _ = -(h b - h a) := by
      rw [integral_neg, integral_deriv_eq_sub (fun x _ => hdiff x)
        (hh.continuous_deriv_one.intervalIntegrable a b)]
    _ = h a - h b := by ring

end intervalIntegral



theorem HasDerivAt.arctan_mul_div {f : ℝ → ℝ} {f' x A B : ℝ}
    (hf : HasDerivAt f f' x) (hB : B ≠ 0) :
    HasDerivAt (fun u => Real.arctan (A * f u / B))
      (A * B * f' / (A ^ 2 * f x ^ 2 + B ^ 2)) x := by
  convert ((hf.const_mul A).div_const B).arctan using 1
  have hden : A ^ 2 * f x ^ 2 + B ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (mul_nonneg (sq_nonneg A) (sq_nonneg (f x)))
      (sq_pos_of_ne_zero hB))
  field_simp
  ring

namespace intervalIntegral



theorem integral_turningDensity_le_pi {f : ℝ → ℝ} {ell A B : ℝ}
    (hf : ContDiff ℝ 1 f) (hell : 0 < ell) (hA : 0 ≤ A) (hB : 0 < B)
    (hzero : f 0 = 0) (hsymm : ∀ x ∈ Icc 0 ell, f (ell - x) = f x)
    (hmono : MonotoneOn f (Icc 0 (ell / 2))) :
    (∫ x in (0 : ℝ)..ell, A * B * |deriv f x| / (A ^ 2 * f x ^ 2 + B ^ 2)) ≤
      Real.pi := by
  let theta : ℝ → ℝ := fun x => Real.arctan (A * f x / B)
  have htheta : ContDiff ℝ 1 theta := ((contDiff_const.mul hf).div_const B).arctan
  have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
  have hden (x : ℝ) : 0 < A ^ 2 * f x ^ 2 + B ^ 2 :=
    add_pos_of_nonneg_of_pos (mul_nonneg (sq_nonneg A) (sq_nonneg (f x)))
      (sq_pos_of_pos hB)
  have hderiv (x : ℝ) :
      |deriv theta x| = A * B * |deriv f x| / (A ^ 2 * f x ^ 2 + B ^ 2) := by
    rw [((hdiff x).hasDerivAt.arctan_mul_div (A := A) hB.ne').deriv]
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg hA, abs_of_pos hB,
      abs_of_pos (hden x)]
  have htheta_mono : MonotoneOn theta (Icc 0 (ell / 2)) := by
    intro x hx y hy hxy
    exact Real.arctan_mono (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hmono hx hy hxy) hA) hB.le)
  have hanti : AntitoneOn f (Icc (ell / 2) ell) := by
    intro x hx y hy hxy
    have hx' : ell - x ∈ Icc 0 (ell / 2) := by
      constructor <;> linarith [hx.1, hx.2]
    have hy' : ell - y ∈ Icc 0 (ell / 2) := by
      constructor <;> linarith [hy.1, hy.2]
    have hxcell : x ∈ Icc 0 ell := ⟨by linarith [hx.1], hx.2⟩
    have hycell : y ∈ Icc 0 ell := ⟨by linarith [hy.1], hy.2⟩
    have h := hmono hy' hx' (by linarith)
    simpa only [hsymm x hxcell, hsymm y hycell] using h
  have htheta_anti : AntitoneOn theta (Icc (ell / 2) ell) := by
    intro x hx y hy hxy
    exact Real.arctan_mono (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hanti hx hy hxy) hA) hB.le)
  have htzero : theta 0 = 0 := by simp [theta, hzero]
  have htell : theta ell = 0 := by
    have he : f ell = 0 := by
      simpa only [sub_zero, hzero] using hsymm 0 ⟨le_rfl, hell.le⟩
    simp [theta, he]
  have hint (a b : ℝ) : IntervalIntegrable (fun x => |deriv theta x|) volume a b :=
    htheta.continuous_deriv_one.abs.intervalIntegrable a b
  have hfirst := integral_abs_deriv_eq_sub_of_monotoneOn htheta
    (half_pos hell) htheta_mono
  have hsecond := integral_abs_deriv_eq_sub_of_antitoneOn htheta
    (show ell / 2 < ell by linarith) htheta_anti
  calc
    (∫ x in (0 : ℝ)..ell, A * B * |deriv f x| / (A ^ 2 * f x ^ 2 + B ^ 2)) =
        ∫ x in (0 : ℝ)..ell, |deriv theta x| := by
      apply integral_congr
      exact fun x _ => (hderiv x).symm
    _ = (∫ x in (0 : ℝ)..(ell / 2), |deriv theta x|) +
        ∫ x in (ell / 2)..ell, |deriv theta x| :=
      (integral_add_adjacent_intervals (hint 0 (ell / 2)) (hint (ell / 2) ell)).symm
    _ = 2 * theta (ell / 2) := by rw [hfirst, hsecond, htzero, htell]; ring
    _ ≤ Real.pi := by
      have h := Real.arctan_lt_pi_div_two (A * f (ell / 2) / B)
      change 2 * Real.arctan (A * f (ell / 2) / B) ≤ Real.pi
      linarith

end intervalIntegral
