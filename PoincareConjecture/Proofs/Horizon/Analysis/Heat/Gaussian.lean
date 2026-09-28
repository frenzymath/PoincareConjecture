import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.FDeriv.Measurable

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Poincare.Analysis.Heat

theorem integrable_abs_standardGaussian :
    Integrable (fun z : ℝ ↦ |z|) (gaussianReal 0 1) := by
  simpa only [id_eq, Real.norm_eq_abs] using
    (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num) |>.norm

theorem integral_sq_standardGaussian :
    (∫ z : ℝ, z ^ 2 ∂gaussianReal 0 1) = 1 := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa only [integral_id_gaussianReal, sub_zero, NNReal.coe_one] using h

theorem integral_abs_standardGaussian_le_one :
    (∫ z : ℝ, |z| ∂gaussianReal 0 1) ≤ 1 := by
  have hsq : Integrable (fun z : ℝ ↦ z ^ 2) (gaussianReal 0 1) := by
    simpa only [id_eq, Real.norm_eq_abs, sq_abs] using
      (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_norm_pow (by norm_num)
  have h := integral_mono integrable_abs_standardGaussian
    ((hsq.add (integrable_const (1 : ℝ))).div_const 2)
    (fun z ↦ show |z| ≤ (z ^ 2 + 1) / 2 by nlinarith [sq_nonneg (|z| - 1), sq_abs z])
  simpa only [Pi.add_apply, integral_div, integral_add hsq (integrable_const (1 : ℝ)),
    integral_sq_standardGaussian, integral_const, probReal_univ, smul_eq_mul,
    one_mul, show (1 + 1) / (2 : ℝ) = 1 by norm_num] using h

noncomputable def gaussianAverage (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  ∫ z, f (x + Real.sqrt (2 * t) * z) ∂ProbabilityTheory.gaussianReal 0 1

theorem integrable_gaussianAverage {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (t x : ℝ) :
    Integrable (fun z ↦ f (x + Real.sqrt (2 * t) * z)) (gaussianReal 0 1) := by
  apply ((integrable_const |f x|).add
    (integrable_abs_standardGaussian.const_mul ((L : ℝ) * Real.sqrt (2 * t)))).mono'
    (hf.continuous.comp (by fun_prop)).aestronglyMeasurable
  filter_upwards [] with z
  have h := hf.dist_le_mul (x + Real.sqrt (2 * t) * z) x
  simp only [Real.dist_eq, add_sub_cancel_left, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg _)] at h
  rw [Real.norm_eq_abs]
  simp only [Function.comp_apply, Pi.add_apply]
  have htri := abs_add_le (f x) (f (x + Real.sqrt (2 * t) * z) - f x)
  simp only [add_sub_cancel] at htri
  nlinarith

theorem lipschitzWith_gaussianAverage {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (t : ℝ) : LipschitzWith L (gaussianAverage f t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hbound : ∀ᵐ z ∂gaussianReal 0 1,
      ‖f (x + Real.sqrt (2 * t) * z) - f (y + Real.sqrt (2 * t) * z)‖ ≤
        (L : ℝ) * dist x y := by
    filter_upwards [] with z
    simpa only [Real.dist_eq, Real.norm_eq_abs, add_sub_add_right_eq_sub] using
      hf.dist_le_mul (x + Real.sqrt (2 * t) * z) (y + Real.sqrt (2 * t) * z)
  have h := norm_integral_le_of_norm_le_const hbound
  rw [integral_sub (integrable_gaussianAverage hf t x)
    (integrable_gaussianAverage hf t y)] at h
  simpa only [gaussianAverage, dist_eq_norm, probReal_univ, mul_one] using h

theorem abs_gaussianAverage_sub_le {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (t x : ℝ) :
    |gaussianAverage f t x - f x| ≤ (L : ℝ) * Real.sqrt (2 * t) := by
  have hbound : ∀ᵐ z ∂gaussianReal 0 1,
      ‖f (x + Real.sqrt (2 * t) * z) - f x‖ ≤
        ((L : ℝ) * Real.sqrt (2 * t)) * |z| := by
    filter_upwards [] with z
    simpa only [Real.dist_eq, Real.norm_eq_abs, add_sub_cancel_left, abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_assoc] using
      hf.dist_le_mul (x + Real.sqrt (2 * t) * z) x
  have h := norm_integral_le_of_norm_le
    (integrable_abs_standardGaussian.const_mul ((L : ℝ) * Real.sqrt (2 * t))) hbound
  rw [integral_sub (integrable_gaussianAverage hf t x) (integrable_const _),
    integral_const_mul] at h
  have havg : |gaussianAverage f t x - f x| ≤
      ((L : ℝ) * Real.sqrt (2 * t)) * ∫ z : ℝ, |z| ∂gaussianReal 0 1 := by
    simpa [gaussianAverage, Real.norm_eq_abs] using h
  exact havg.trans (by
    simpa using mul_le_mul_of_nonneg_left integral_abs_standardGaussian_le_one
      (show 0 ≤ (L : ℝ) * Real.sqrt (2 * t) by positivity))

theorem gaussianAverage_estimates {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) {t : ℝ} (ht : 0 ≤ t) :
    (∀ x, Integrable (fun z ↦ f (x + Real.sqrt (2 * t) * z))
      (ProbabilityTheory.gaussianReal 0 1)) ∧
    LipschitzWith L (gaussianAverage f t) ∧
    (∀ x, |gaussianAverage f t x - f x| ≤ (L : ℝ) * Real.sqrt (2 * t)) := by
  have _ := ht
  exact ⟨integrable_gaussianAverage hf t, lipschitzWith_gaussianAverage hf t,
    abs_gaussianAverage_sub_le hf t⟩

theorem tendstoUniformly_gaussianAverage {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) :
    TendstoUniformly (gaussianAverage f) f (𝓝[>] (0 : ℝ)) := by
  have hlim : Tendsto (fun t : ℝ ↦ (L : ℝ) * Real.sqrt (2 * t))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont : Continuous (fun t : ℝ ↦ (L : ℝ) * Real.sqrt (2 * t)) := by fun_prop
    simpa using (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with t ht
  intro x
  rw [Real.dist_eq, abs_sub_comm]
  exact (abs_gaussianAverage_sub_le hf t x).trans_lt ht

theorem hasDerivAt_gaussianAverage {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (hdf : Differentiable ℝ f) (t x : ℝ) :
    HasDerivAt (gaussianAverage f t) (gaussianAverage (deriv f) t x) x := by
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (s := Set.univ) (bound := fun _ : ℝ ↦ (L : ℝ))
    (F := fun a z : ℝ ↦ f (a + Real.sqrt (2 * t) * z))
    (F' := fun a z : ℝ ↦ deriv f (a + Real.sqrt (2 * t) * z))
    (x₀ := x) (Filter.univ_mem) ?_ (integrable_gaussianAverage hf t x) ?_ ?_
    (integrable_const _) ?_
  · exact h.2
  · exact Filter.Eventually.of_forall fun a ↦
      (integrable_gaussianAverage hf t a).aestronglyMeasurable
  · exact ((measurable_deriv f).comp (by fun_prop)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun z a _ ↦ norm_deriv_le_of_lipschitz hf
  · filter_upwards [] with z
    intro a _
    simpa only [mul_one, Function.comp_def, id_eq] using!
      (hdf (a + Real.sqrt (2 * t) * z)).hasDerivAt.comp a
        ((hasDerivAt_id a).add_const (Real.sqrt (2 * t) * z))

theorem abs_deriv_gaussianAverage_le {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (t x : ℝ) :
    |deriv (gaussianAverage f t) x| ≤ (L : ℝ) := by
  simpa only [Real.norm_eq_abs] using
    norm_deriv_le_of_lipschitz (x₀ := x) (lipschitzWith_gaussianAverage hf t)

end Poincare.Analysis.Heat
