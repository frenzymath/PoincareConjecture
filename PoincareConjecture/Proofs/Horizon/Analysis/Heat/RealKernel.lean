import PoincareConjecture.Proofs.Horizon.Analysis.Heat.Gaussian
import Mathlib.Analysis.SpecialFunctions.Sqrt











set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ContDiff NNReal

namespace Poincare.Analysis.Heat

noncomputable def realHeatKernel (t x : ℝ) : ℝ :=
  (Real.sqrt (4 * Real.pi * t))⁻¹ * Real.exp (-x ^ 2 / (4 * t))

theorem realHeatKernel_eq_gaussianPDFReal {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    realHeatKernel t x = gaussianPDFReal 0 ⟨2 * t, by positivity⟩ x := by
  change (Real.sqrt (4 * Real.pi * t))⁻¹ * Real.exp (-x ^ 2 / (4 * t)) =
    (Real.sqrt (2 * Real.pi * (2 * t)))⁻¹ * Real.exp (-(x - 0) ^ 2 / (2 * (2 * t)))
  congr 3 <;> ring

theorem integrable_realHeatKernel {t : ℝ} (ht : 0 < t) :
    Integrable (realHeatKernel t) := by
  have heq : realHeatKernel t = gaussianPDFReal 0 ⟨2 * t, by positivity⟩ :=
    funext (realHeatKernel_eq_gaussianPDFReal ht.le)
  rw [heq]
  exact integrable_gaussianPDFReal _ _

theorem integral_realHeatKernel {t : ℝ} (ht : 0 < t) :
    (∫ x, realHeatKernel t x) = 1 := by
  simp_rw [realHeatKernel_eq_gaussianPDFReal ht.le]
  apply integral_gaussianPDFReal_eq_one
  apply ne_of_gt
  change 0 < 2 * t
  positivity

theorem realHeatKernel_pos {t : ℝ} (ht : 0 < t) (x : ℝ) :
    0 < realHeatKernel t x := by
  unfold realHeatKernel
  positivity

theorem hasDerivAt_realHeatKernel_space {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (realHeatKernel t) (-x / (2 * t) * realHeatKernel t x) x := by
  have h := (((hasDerivAt_id x).pow 2).neg.div_const (4 * t)).exp.const_mul
    (Real.sqrt (4 * Real.pi * t))⁻¹
  convert! h using 1
  simp only [realHeatKernel, id_eq, Nat.cast_ofNat, mul_one, Pi.neg_apply,
    Pi.pow_apply]
  field_simp
  ring

theorem deriv_realHeatKernel_space {t : ℝ} (ht : 0 < t) :
    deriv (realHeatKernel t) = fun x ↦ -x / (2 * t) * realHeatKernel t x := by
  funext x
  exact (hasDerivAt_realHeatKernel_space ht x).deriv

theorem hasDerivAt_realHeatKernel_space_twice {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (deriv (realHeatKernel t))
      ((x ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * realHeatKernel t x) x := by
  rw [deriv_realHeatKernel_space ht]
  have h := ((hasDerivAt_id x).neg.div_const (2 * t)).mul
    (hasDerivAt_realHeatKernel_space ht x)
  convert! h using 1
  simp only [Pi.neg_apply, id_eq]
  field_simp
  ring

theorem hasDerivAt_realHeatKernel_time {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s ↦ realHeatKernel s x)
      ((x ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * realHeatKernel t x) t := by
  have hp : 0 < 4 * Real.pi * t := by positivity
  have hs : Real.sqrt (4 * Real.pi * t) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have hn := (((hasDerivAt_id t).const_mul (4 * Real.pi)).sqrt hp.ne').inv hs
  have he := ((hasDerivAt_const t (-x ^ 2)).div
    ((hasDerivAt_id t).const_mul 4) (by positivity : (4 : ℝ) * t ≠ 0)).exp
  have h := hn.mul he
  convert! h using 1
  simp only [realHeatKernel, id_eq, mul_one, zero_mul, zero_sub, Pi.div_apply,
    Pi.inv_apply]
  field_simp
  rw [Real.sq_sqrt (by positivity : 0 ≤ 4 * t * Real.pi)]
  ring

theorem realHeatKernel_properties {t : ℝ} (ht : 0 < t) :
    Integrable (realHeatKernel t) ∧
    (∫ x, realHeatKernel t x) = 1 ∧
    (∀ x, 0 < realHeatKernel t x) ∧
    (∀ x, HasDerivAt (fun s ↦ realHeatKernel s x)
      (deriv (deriv (realHeatKernel t)) x) t) := by
  refine ⟨integrable_realHeatKernel ht, integral_realHeatKernel ht, realHeatKernel_pos ht, ?_⟩
  intro x
  rw [(hasDerivAt_realHeatKernel_space_twice ht x).deriv]
  exact hasDerivAt_realHeatKernel_time ht x

theorem contDiffOn_realHeatKernel :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ ↦ realHeatKernel p.1 p.2)
      {p : ℝ × ℝ | 0 < p.1} := by
  apply ContDiffOn.mul
  · apply ContDiffOn.inv
    · apply ContDiffOn.sqrt
      · fun_prop
      · intro p hp
        change 0 < p.1 at hp
        positivity
    · intro p hp
      change 0 < p.1 at hp
      exact (Real.sqrt_pos.mpr (by positivity)).ne'
  · apply ContDiffOn.exp
    apply ContDiffOn.div
    · fun_prop
    · fun_prop
    · intro p hp
      change 0 < p.1 at hp
      positivity



theorem gaussianAverage_eq_integral_realHeatKernel {f : ℝ → ℝ}
    (hf : Continuous f) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    gaussianAverage f t x = ∫ y, realHeatKernel t (y - x) * f y := by
  let v : ℝ≥0 := ⟨2 * t, by positivity⟩
  have hv : v ≠ 0 := by
    apply ne_of_gt
    change 0 < 2 * t
    positivity
  have hmap : (gaussianReal 0 1).map (fun z ↦ x + Real.sqrt (2 * t) * z) =
      gaussianReal x v := by
    change (gaussianReal 0 1).map ((fun y ↦ x + y) ∘
      (fun z ↦ Real.sqrt (2 * t) * z)) = gaussianReal x v
    rw [← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
      gaussianReal_map_const_add]
    simp only [mul_zero, zero_add, mul_one]
    congr 1
    apply Subtype.ext
    exact Real.sq_sqrt (by positivity)
  calc
    gaussianAverage f t x = ∫ y, f y ∂gaussianReal x v := by
      rw [← hmap, integral_map (by fun_prop) hf.aestronglyMeasurable]
      rfl
    _ = ∫ y, gaussianPDFReal x v y * f y :=
      integral_gaussianReal_eq_integral_smul hv
    _ = ∫ y, realHeatKernel t (y - x) * f y := by
      apply integral_congr_ae
      filter_upwards [] with y
      congr 1
      change (Real.sqrt (2 * Real.pi * (2 * t)))⁻¹ *
          Real.exp (-(y - x) ^ 2 / (2 * (2 * t))) =
        (Real.sqrt (4 * Real.pi * t))⁻¹ * Real.exp (-(y - x) ^ 2 / (4 * t))
      congr 3 <;> ring

theorem integrable_pow_mul_realHeatKernel {t : ℝ} (ht : 0 < t) (m : ℕ) :
    Integrable (fun x ↦ x ^ m * realHeatKernel t x) := by
  have h := (integrable_rpow_mul_exp_neg_mul_sq
    (by positivity : 0 < (4 * t)⁻¹) (s := (m : ℝ))
    (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg m))).const_mul
    (Real.sqrt (4 * Real.pi * t))⁻¹
  simp only [Real.rpow_natCast] at h
  convert! h using 1
  ext x
  simp only [realHeatKernel]
  rw [show -x ^ 2 / (4 * t) = -(4 * t)⁻¹ * x ^ 2 by ring]
  ring

theorem integral_abs_mul_realHeatKernel_le {t : ℝ} (ht : 0 < t) :
    (∫ x, |x| * realHeatKernel t x) ≤ Real.sqrt (2 * t) := by
  have hf : LipschitzWith 1 (fun x : ℝ ↦ |x|) := by
    simpa only [← Real.norm_eq_abs] using!
      (lipschitzWith_one_norm : LipschitzWith 1 (norm : ℝ → ℝ))
  have h := abs_gaussianAverage_sub_le hf t 0
  rw [gaussianAverage_eq_integral_realHeatKernel hf.continuous ht 0] at h
  simp only [sub_zero, abs_zero, NNReal.coe_one, one_mul] at h
  have heq : (∫ x, |x| * realHeatKernel t x) = ∫ x, realHeatKernel t x * |x| := by
    congr 1
    ext x
    ring
  rw [heq]
  exact (le_abs_self _).trans h

theorem integral_sq_mul_realHeatKernel {t : ℝ} (ht : 0 < t) :
    (∫ x, x ^ 2 * realHeatKernel t x) = 2 * t := by
  have h := gaussianAverage_eq_integral_realHeatKernel
    (f := fun x : ℝ ↦ x ^ 2) (by fun_prop) ht 0
  simp only [gaussianAverage, zero_add, sub_zero, mul_pow, integral_const_mul,
    integral_sq_standardGaussian, mul_one, Real.sq_sqrt (by positivity : 0 ≤ 2 * t)] at h
  rw [h]
  congr 1
  ext x
  ring

theorem integrable_deriv_realHeatKernel {t : ℝ} (ht : 0 < t) :
    Integrable (deriv (realHeatKernel t)) := by
  rw [deriv_realHeatKernel_space ht]
  convert! (integrable_pow_mul_realHeatKernel ht 1).const_mul (-1 / (2 * t)) using 1
  ext x
  simp only [pow_one]
  ring

theorem integral_abs_deriv_realHeatKernel_le {t : ℝ} (ht : 0 < t) :
    (∫ x, |deriv (realHeatKernel t) x|) ≤ (Real.sqrt (2 * t))⁻¹ := by
  have heq : (fun x ↦ |deriv (realHeatKernel t) x|) =
      fun x ↦ (2 * t)⁻¹ * (|x| * realHeatKernel t x) := by
    funext x
    rw [deriv_realHeatKernel_space ht]
    simp only [abs_mul, abs_div, abs_neg, abs_of_pos (by positivity : 0 < 2 * t),
      abs_of_pos (realHeatKernel_pos ht x)]
    ring
  rw [heq, integral_const_mul]
  calc
    (2 * t)⁻¹ * (∫ x, |x| * realHeatKernel t x) ≤ (2 * t)⁻¹ * Real.sqrt (2 * t) :=
      mul_le_mul_of_nonneg_left (integral_abs_mul_realHeatKernel_le ht) (by positivity)
    _ = (Real.sqrt (2 * t))⁻¹ := by
      have hs := Real.sq_sqrt (by positivity : 0 ≤ 2 * t)
      have hp : 0 < Real.sqrt (2 * t) := by positivity
      field_simp
      nlinarith

theorem integrable_deriv_realHeatKernel_twice {t : ℝ} (ht : 0 < t) :
    Integrable (deriv (deriv (realHeatKernel t))) := by
  have h := ((integrable_pow_mul_realHeatKernel ht 2).div_const (4 * t ^ 2)).sub
    ((integrable_realHeatKernel ht).div_const (2 * t))
  convert! h using 1
  ext x
  rw [(hasDerivAt_realHeatKernel_space_twice ht x).deriv]
  simp only [Pi.sub_apply]
  ring

theorem integral_abs_deriv_realHeatKernel_twice_le {t : ℝ} (ht : 0 < t) :
    (∫ x, |deriv (deriv (realHeatKernel t)) x|) ≤ t⁻¹ := by
  have hmajor := ((integrable_pow_mul_realHeatKernel ht 2).div_const (4 * t ^ 2)).add
    ((integrable_realHeatKernel ht).div_const (2 * t))
  have hbound : ∀ x, |deriv (deriv (realHeatKernel t)) x| ≤
      x ^ 2 * realHeatKernel t x / (4 * t ^ 2) + realHeatKernel t x / (2 * t) := by
    intro x
    rw [(hasDerivAt_realHeatKernel_space_twice ht x).deriv, sub_mul]
    have h := abs_sub_le (x ^ 2 / (4 * t ^ 2) * realHeatKernel t x) 0
      (1 / (2 * t) * realHeatKernel t x)
    have hk := (realHeatKernel_pos ht x).le
    simp only [sub_zero, zero_sub, abs_neg] at h
    rw [abs_of_nonneg (show 0 ≤ x ^ 2 / (4 * t ^ 2) * realHeatKernel t x
        from mul_nonneg (by positivity) hk),
      abs_of_nonneg (show 0 ≤ 1 / (2 * t) * realHeatKernel t x
        from mul_nonneg (by positivity) hk)] at h
    simpa only [div_mul_eq_mul_div, one_mul] using h
  have hi := integral_mono (integrable_deriv_realHeatKernel_twice ht).abs hmajor hbound
  simp only [Pi.add_apply, integral_add
      ((integrable_pow_mul_realHeatKernel ht 2).div_const (4 * t ^ 2))
      ((integrable_realHeatKernel ht).div_const (2 * t)),
    integral_div, integral_sq_mul_realHeatKernel ht, integral_realHeatKernel ht] at hi
  convert! hi using 1
  field_simp
  ring

end Poincare.Analysis.Heat
