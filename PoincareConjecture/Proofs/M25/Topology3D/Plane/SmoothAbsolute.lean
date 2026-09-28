import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Basic











set_option autoImplicit false

open Set Metric Function MeasureTheory ContinuousLinearMap
open scoped ContDiff Convolution

namespace PoincareConjecture.M25.Topology3D



theorem exists_smooth_absolute_rounding {δ : ℝ} (hδ : 0 < δ) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ ∧
      (∀ x, ρ (-x) = ρ x) ∧ LipschitzWith 1 ρ ∧
      (∀ x, δ ≤ |x| → ρ x = |x|) ∧
      (∀ x, |x| ≤ ρ x ∧ ρ x ≤ |x| + δ) ∧
      ∀ x, |deriv ρ x| ≤ 1 := by
  let φ : ContDiffBump (0 : ℝ) :=
    ⟨δ / 2, δ, div_pos hδ (by norm_num), by linarith⟩
  let k : ℝ → ℝ := φ.normed volume
  have hk0 (t : ℝ) : 0 ≤ k t := φ.nonneg_normed t
  have hkeven (t : ℝ) : k (-t) = k t := φ.normed_neg t
  have hksmooth : ContDiff ℝ ∞ k := φ.contDiff_normed
  have hkcont : Continuous k := φ.continuous_normed
  have hkcs : HasCompactSupport k := φ.hasCompactSupport_normed
  have hkI : Integrable k := φ.integrable_normed
  have hkone : ∫ t : ℝ, k t = 1 := φ.integral_normed
  have hksupport : support k = ball (0 : ℝ) δ := φ.support_normed_eq
  have hmI : Integrable (fun t : ℝ => k t * t) :=
    (hkcont.mul continuous_id).integrable_of_hasCompactSupport hkcs.mul_right
  have hI (x : ℝ) : Integrable (fun t : ℝ => k t * |x - t|) :=
    (hkcont.mul (continuous_const.sub continuous_id).abs).integrable_of_hasCompactSupport
      hkcs.mul_right
  have hmoment : ∫ t : ℝ, k t * t = 0 := by
    have hm : (∫ t : ℝ, k t * t) = -(∫ t : ℝ, k t * t) := by
      calc
        (∫ t : ℝ, k t * t) = ∫ t : ℝ, k (-t) * (-t) :=
          (integral_neg_eq_self (fun t : ℝ => k t * t) volume).symm
        _ = -(∫ t : ℝ, k t * t) := by
          simp_rw [hkeven, mul_neg]
          exact integral_neg _
    linarith
  have hlinear (x : ℝ) : ∫ t : ℝ, k t * (x - t) = x := by
    simp_rw [mul_sub]
    rw [integral_sub (hkI.mul_const x) hmI, integral_mul_const, hkone, hmoment,
      one_mul, sub_zero]
  let ρ : ℝ → ℝ := fun x => ∫ t : ℝ, k t * |x - t|
  have hρeq : ρ = (k ⋆[lsmul ℝ ℝ, volume] abs) := by
    funext x
    simp only [ρ, convolution_def, lsmul_apply, smul_eq_mul]
  have hρ : ContDiff ℝ ∞ ρ := by
    rw [hρeq]
    exact hkcs.contDiff_convolution_left (lsmul ℝ ℝ) (n := ⊤) hksmooth
      continuous_abs.locallyIntegrable
  have heven (x : ℝ) : ρ (-x) = ρ x := by
    change (∫ t : ℝ, k t * |-x - t|) = ∫ t : ℝ, k t * |x - t|
    rw [← integral_neg_eq_self (fun t : ℝ => k t * |-x - t|) volume]
    apply integral_congr_ae
    filter_upwards [] with t
    rw [hkeven, show -x - -t = -(x - t) by ring, abs_neg]
  have hpositive (x : ℝ) (hx : δ ≤ x) : ρ x = x := by
    calc
      ρ x = ∫ t : ℝ, k t * (x - t) := by
        apply integral_congr_ae
        filter_upwards [] with t
        by_cases hkt : k t = 0
        · simp only [hkt, zero_mul]
        · have ht : t ∈ support k := hkt
          rw [hksupport] at ht
          have htδ : |t| < δ := by
            simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs] using ht
          rw [abs_of_nonneg (sub_nonneg.mpr ((le_abs_self t).trans (htδ.le.trans hx)))]
      _ = x := hlinear x
  have hlower (x : ℝ) : |x| ≤ ρ x := by
    calc
      |x| = |∫ t : ℝ, k t * (x - t)| := congrArg abs (hlinear x).symm
      _ ≤ ∫ t : ℝ, |k t * (x - t)| := abs_integral_le_integral_abs
      _ = ρ x := by
        apply integral_congr_ae
        filter_upwards [] with t
        rw [abs_mul, abs_of_nonneg (hk0 t)]
  have hdiff (x y : ℝ) : |ρ x - ρ y| ≤ |x - y| := by
    have heq : ρ x - ρ y = ∫ t : ℝ, k t * (|x - t| - |y - t|) := by
      calc
        ρ x - ρ y = ∫ t : ℝ, k t * |x - t| - k t * |y - t| :=
          (integral_sub (hI x) (hI y)).symm
        _ = _ := by
          apply integral_congr_ae
          filter_upwards [] with t
          ring
    have hb : ‖∫ t : ℝ, k t * (|x - t| - |y - t|)‖ ≤
        ∫ t : ℝ, k t * |x - y| := by
      apply norm_integral_le_of_norm_le (hkI.mul_const |x - y|)
      filter_upwards [] with t
      have hxy : x - t - (y - t) = x - y := by ring
      have habs : abs (|x - t| - |y - t|) ≤ |x - y| := by
        simpa only [Real.norm_eq_abs, hxy] using norm_abs_sub_abs (x - t) (y - t)
      simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hk0 t)] using
        mul_le_mul_of_nonneg_left habs (hk0 t)
    rw [heq]
    simpa only [Real.norm_eq_abs, integral_mul_const, hkone, one_mul] using hb
  have hLip : LipschitzWith 1 ρ := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hdiff x y
  have happrox (x : ℝ) : abs (ρ x - |x|) ≤ δ := by
    have hb : ∀ y ∈ ball x φ.rOut, dist (|y|) (|x|) ≤ δ := by
      intro y hy
      have hyδ : dist y x < δ := mem_ball.mp hy
      have habs : dist (|y|) (|x|) ≤ dist y x := by
        simpa only [dist_eq_norm] using norm_abs_sub_abs y x
      exact habs.trans hyδ.le
    have h := ContDiffBump.dist_normed_convolution_le (φ := φ) (μ := volume)
      continuous_abs.aestronglyMeasurable hb
    simpa only [ρ, k, convolution_def, lsmul_apply, smul_eq_mul, Real.dist_eq] using h
  refine ⟨ρ, hρ, heven, hLip, ?_, ?_, ?_⟩
  · intro x hx
    by_cases hx0 : 0 ≤ x
    · rw [abs_of_nonneg hx0] at hx ⊢
      exact hpositive x hx
    · have hxneg : x < 0 := lt_of_not_ge hx0
      rw [abs_of_neg hxneg] at hx ⊢
      rw [← heven x]
      exact hpositive (-x) hx
  · intro x
    refine ⟨hlower x, ?_⟩
    linarith [le_abs_self (ρ x - |x|), happrox x]
  · intro x
    simpa only [Real.norm_eq_abs, NNReal.coe_one] using
      norm_deriv_le_of_lipschitz (x₀ := x) hLip

end PoincareConjecture.M25.Topology3D
