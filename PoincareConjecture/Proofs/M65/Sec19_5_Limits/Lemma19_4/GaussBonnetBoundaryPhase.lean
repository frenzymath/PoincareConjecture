import Mathlib.MeasureTheory.Integral.CircleIntegral










set_option autoImplicit false

open Complex Real
open scoped Topology ComplexConjugate

namespace PoincareConjecture.M65Gauss



theorem boundary_phase_sq {a z : ℂ} (ha : ‖a‖ = 1) (hz : ‖z‖ = 1)
    (hne : z ≠ a) : ((z - a) / (‖z - a‖ : ℂ)) ^ 2 = -z * a := by
  have hua : a * conj a = 1 := by simpa only [ha, one_pow, ofReal_one] using mul_conj' a
  have huz : z * conj z = 1 := by simpa only [hz, one_pow, ofReal_one] using mul_conj' z
  have hc : (-z * a) * conj (z - a) = z - a := by
    calc
      (-z * a) * conj (z - a) = z * (a * conj a) - a * (z * conj z) := by
        rw [map_sub]
        ring
      _ = z - a := by rw [hua, huz, mul_one, mul_one]
  have hs : (z - a) ^ 2 = (-z * a) * (‖z - a‖ : ℂ) ^ 2 := by
    rw [← mul_conj' (z - a)]
    calc
      (z - a) ^ 2 = (z - a) * ((-z * a) * conj (z - a)) := by rw [hc, pow_two]
      _ = (-z * a) * ((z - a) * conj (z - a)) := by ring
  rw [div_pow, hs]
  exact mul_div_cancel_right₀ _ (pow_ne_zero _ (ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr
    (sub_ne_zero.mpr hne))))




theorem boundary_phase_even {a z : ℂ} (ha : ‖a‖ = 1) (hz : ‖z‖ = 1)
    (hne : z ≠ a) (k : ℕ) :
    ((z - a) / (‖z - a‖ : ℂ)) ^ (2 * k) = (-z * a) ^ k := by
  rw [pow_mul, boundary_phase_sq ha hz hne]




theorem hasDerivAt_boundary_phase (a : ℂ) (k : ℕ) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => (-circleMap 0 1 t * a) ^ k)
      (Complex.I * (k : ℂ) * (-circleMap 0 1 θ * a) ^ k) θ := by
  have h := ((hasDerivAt_circleMap 0 1 θ).neg.mul_const a).pow k
  change HasDerivAt (fun t : ℝ => (-circleMap 0 1 t * a) ^ k)
    ((k : ℂ) * (-circleMap 0 1 θ * a) ^ (k - 1) *
      (-(circleMap 0 1 θ * I) * a)) θ at h
  convert h using 1
  cases k with
  | zero => simp
  | succ k => simp only [Nat.succ_sub_one, pow_succ]; ring




theorem boundary_phase_rotation_integral {a : ℂ} (ha : ‖a‖ = 1) (k : ℕ) :
    (∫ θ in (-Real.pi)..Real.pi,
      (deriv (fun t : ℝ => (-circleMap 0 1 t * a) ^ k) θ /
        (-circleMap 0 1 θ * a) ^ k).im) = 2 * Real.pi * k := by
  have hnorm (θ : ℝ) : ‖(-circleMap 0 1 θ * a) ^ k‖ = 1 := by
    simp only [norm_pow, norm_mul, norm_neg, norm_circleMap_zero, abs_one, ha,
      one_mul, one_pow]
  have heq (θ : ℝ) :
      (deriv (fun t : ℝ => (-circleMap 0 1 t * a) ^ k) θ /
        (-circleMap 0 1 θ * a) ^ k).im = (k : ℝ) := by
    rw [(hasDerivAt_boundary_phase a k θ).deriv,
      mul_div_cancel_right₀ _ (norm_ne_zero_iff.mp (by rw [hnorm]; norm_num))]
    simp
  simp only [heq, intervalIntegral.integral_const, sub_neg_eq_add, smul_eq_mul]
  ring

end PoincareConjecture.M65Gauss
