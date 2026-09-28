import PoincareConjecture.Proofs.M35.RadialGauge.WeightedKernelEnd
import PoincareConjecture.Proofs.M35.RadialGauge.HeatTimeGain

set_option autoImplicit false

open Set MeasureTheory ProbabilityTheory
open scoped Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ} {A F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem heatAverage_weighted_vanishes_uniformly
    {f : A → V → F} {C T : ℝ}
    (hf : ∀ a, Continuous (f a))
    (hbound : ∀ a x, (1 + ‖x‖) * ‖f a x‖ ≤ C)
    (hend : ∀ e : ℝ, 0 < e → ∃ R : ℝ, ∀ a x,
      R ≤ ‖x‖ → (1 + ‖x‖) * ‖f a x‖ < e) :
    ∀ e : ℝ, 0 < e → ∃ R : ℝ, ∀ a t, t ∈ Icc 0 T → ∀ x, R ≤ ‖x‖ →
      (1 + ‖x‖) * ‖heatAverage t (f a) x‖ < e := by
  intro e he
  obtain ⟨R, hR⟩ := weighted_gaussian_moment_vanishes_uniformly
    (Real.sqrt_nonneg (2 * T)) hf hbound hend (q := fun _ => 1)
    (fun _ => zero_le_one) (integrable_const 1)
    (by simpa only [one_mul, id_eq] using (IsGaussian.integrable_id (μ := stdGaussian V)).norm) e he
  refine ⟨R, fun a t ht x hx => ?_⟩
  have hb : Real.sqrt (2 * t) ∈ Icc 0 (Real.sqrt (2 * T)) :=
    ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left ht.2 (by norm_num))⟩
  have h := hR a (Real.sqrt (2 * t)) hb x hx
  calc
    _ ≤ (1 + ‖x‖) * ∫ z, ‖f a (x + Real.sqrt (2 * t) • z)‖ ∂stdGaussian V :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ = ∫ z, (1 : ℝ) * ((1 + ‖x‖) * ‖f a (x + Real.sqrt (2 * t) • z)‖)
        ∂stdGaussian V := by simp only [one_mul]; rw [integral_const_mul]
    _ < e := h

theorem heatGradientKernel_weighted_vanishes_uniformly
    {f : A → V → F} {C T : ℝ}
    (hf : ∀ a, Continuous (f a))
    (hbound : ∀ a x, (1 + ‖x‖) * ‖f a x‖ ≤ C)
    (hend : ∀ e : ℝ, 0 < e → ∃ R : ℝ, ∀ a x,
      R ≤ ‖x‖ → (1 + ‖x‖) * ‖f a x‖ < e) :
    ∀ e : ℝ, 0 < e → ∃ R : ℝ, ∀ a t, t ∈ Ioc 0 T → ∀ x, R ≤ ‖x‖ →
      (1 + ‖x‖) * ‖heatGradientKernel t (f a) x‖ ≤ e * t ^ (-(1 / 2 : ℝ)) := by
  intro e he
  have hqzi : Integrable (fun z : V => ‖z‖ * ‖z‖) (stdGaussian V) := by
    simpa only [pow_two, id_eq] using
      (IsGaussian.memLp_two_id (μ := stdGaussian V)).integrable_norm_pow (by norm_num)
  have hqni : Integrable (fun z : V => ‖z‖) (stdGaussian V) := by
    simpa only [id_eq] using (IsGaussian.integrable_id (μ := stdGaussian V)).norm
  obtain ⟨R, hR⟩ := weighted_gaussian_moment_vanishes_uniformly
    (Real.sqrt_nonneg (2 * T)) hf hbound hend (fun z : V => norm_nonneg z)
    hqni hqzi e he
  refine ⟨R, fun a t ht x hx => ?_⟩
  let r := Real.sqrt (2 * t)
  have hr : 0 < r := Real.sqrt_pos.mpr (by linarith [ht.1])
  have hb : r ∈ Icc 0 (Real.sqrt (2 * T)) :=
    ⟨hr.le, Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left ht.2 (by norm_num))⟩
  have hsmall := hR a r hb x hx
  let K (z : V) := (innerSL ℝ z).smulRight (f a (x + r • z))
  have hnorm : (1 + ‖x‖) * ‖∫ z, K z ∂stdGaussian V‖ ≤
      ∫ z, ‖z‖ * ((1 + ‖x‖) * ‖f a (x + r • z)‖) ∂stdGaussian V := by
    calc
      _ ≤ (1 + ‖x‖) * ∫ z, ‖K z‖ ∂stdGaussian V :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
      _ = _ := by
        rw [← integral_const_mul]
        congr 1
        funext z
        simp only [K, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
        ring
  have hinv : r⁻¹ ≤ t ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_neg ht.1.le, ← Real.sqrt_eq_rpow]
    exact (inv_le_inv₀ hr (Real.sqrt_pos.mpr ht.1)).mpr
      (Real.sqrt_le_sqrt (by linarith [ht.1]))
  change (1 + ‖x‖) * ‖r⁻¹ • ∫ z, K z ∂stdGaussian V‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  calc
    _ = r⁻¹ * ((1 + ‖x‖) * ‖∫ z, K z ∂stdGaussian V‖) := by ring
    _ ≤ r⁻¹ * (∫ z, ‖z‖ * ((1 + ‖x‖) * ‖f a (x + r • z)‖) ∂stdGaussian V) :=
      mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr hr.le)
    _ ≤ r⁻¹ * e := mul_le_mul_of_nonneg_left hsmall.le (inv_nonneg.mpr hr.le)
    _ ≤ e * t ^ (-(1 / 2 : ℝ)) := by nlinarith [mul_le_mul_of_nonneg_right hinv he.le]

end PoincareConjecture.M35.RadialGauge
