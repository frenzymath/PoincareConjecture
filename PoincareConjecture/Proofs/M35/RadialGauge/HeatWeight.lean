import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Fernique












set_option autoImplicit false

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "V" => EuclideanSpace ℝ (Fin n)


noncomputable def heatAverage (t : ℝ) (f : V → F) (x : V) : F :=
  ∫ z, f (x + Real.sqrt (2 * t) • z) ∂stdGaussian V


noncomputable def gaussianFirstMoment (n : ℕ) : ℝ :=
  ∫ z : EuclideanSpace ℝ (Fin n), ‖z‖ ∂stdGaussian (EuclideanSpace ℝ (Fin n))

theorem gaussianFirstMoment_nonneg : 0 ≤ gaussianFirstMoment n :=
  integral_nonneg (fun _ => norm_nonneg _)


theorem radial_weight_translation (x z : V) {a : ℝ} (ha : 0 ≤ a) :
    1 + ‖x‖ ≤ (1 + ‖x + a • z‖) * (1 + a * ‖z‖) := by
  have h := norm_sub_le (x + a • z) (a • z)
  rw [add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha] at h
  have hprod : 0 ≤ ‖x + a • z‖ * (a * ‖z‖) := by positivity
  nlinarith

omit [NormedSpace ℝ F] in
private theorem norm_le_of_weighted_bound {f : V → F} {C : ℝ}
    (hf : ∀ x, (1 + ‖x‖) * ‖f x‖ ≤ C) (x : V) : ‖f x‖ ≤ C := by
  nlinarith [hf x, mul_nonneg (norm_nonneg x) (norm_nonneg (f x))]

omit [NormedSpace ℝ F] in


theorem heatAverage_integrable {f : V → F} (hf : Continuous f) {C : ℝ}
    (hbound : ∀ x, (1 + ‖x‖) * ‖f x‖ ≤ C) (t : ℝ) (x : V) :
    Integrable (fun z => f (x + Real.sqrt (2 * t) • z)) (stdGaussian V) := by
  have hc : Continuous (fun z => f (x + Real.sqrt (2 * t) • z)) := hf.comp (by fun_prop)
  apply Integrable.mono' (integrable_const C) hc.aestronglyMeasurable
  exact Eventually.of_forall (fun z => norm_le_of_weighted_bound hbound _)



theorem heatAverage_weighted_norm_le {f : V → F} (hf : Continuous f)
    {C : ℝ} (hbound : ∀ x, (1 + ‖x‖) * ‖f x‖ ≤ C)
    (t : ℝ) (x : V) :
    (1 + ‖x‖) * ‖heatAverage t f x‖ ≤
      C * (1 + Real.sqrt (2 * t) * gaussianFirstMoment n) := by
  let a := Real.sqrt (2 * t)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hint := heatAverage_integrable hf hbound t x
  have hmoment : Integrable (fun z : V => ‖z‖) (stdGaussian V) :=
    IsGaussian.integrable_id.norm
  have hmajor : Integrable (fun z : V => C * (1 + a * ‖z‖)) (stdGaussian V) :=
    ((integrable_const 1).add (hmoment.const_mul a)).const_mul C
  have hpoint (z : V) : (1 + ‖x‖) * ‖f (x + a • z)‖ ≤ C * (1 + a * ‖z‖) := by
    calc
      _ ≤ ((1 + ‖x + a • z‖) * (1 + a * ‖z‖)) * ‖f (x + a • z)‖ :=
        mul_le_mul_of_nonneg_right (radial_weight_translation x z ha) (norm_nonneg _)
      _ = ((1 + ‖x + a • z‖) * ‖f (x + a • z)‖) * (1 + a * ‖z‖) := by ring
      _ ≤ C * (1 + a * ‖z‖) :=
        mul_le_mul_of_nonneg_right (hbound _) (by positivity)
  calc
    (1 + ‖x‖) * ‖heatAverage t f x‖ ≤
        (1 + ‖x‖) * ∫ z, ‖f (x + a • z)‖ ∂stdGaussian V :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ = ∫ z, (1 + ‖x‖) * ‖f (x + a • z)‖ ∂stdGaussian V :=
      (integral_const_mul _ _).symm
    _ ≤ ∫ z : V, C * (1 + a * ‖z‖) ∂stdGaussian V :=
      integral_mono (hint.norm.const_mul _) hmajor hpoint
    _ = C * (1 + Real.sqrt (2 * t) * gaussianFirstMoment n) := by
      rw [integral_const_mul, integral_add (integrable_const 1) (hmoment.const_mul a),
        integral_const_mul]
      simp [a, gaussianFirstMoment]



theorem heatAverage_weighted_norm_le_on_slab {f : V → F} (hf : Continuous f)
    {C T : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, (1 + ‖x‖) * ‖f x‖ ≤ C)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : V) :
    (1 + ‖x‖) * ‖heatAverage t f x‖ ≤
      C * (1 + Real.sqrt (2 * T) * gaussianFirstMoment n) := by
  apply (heatAverage_weighted_norm_le hf hbound t x).trans
  exact mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left ht.2 (by norm_num)))
      gaussianFirstMoment_nonneg)) hC

end PoincareConjecture.M35.RadialGauge
