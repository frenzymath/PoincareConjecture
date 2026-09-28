import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.MeanValue.LowerDerivative
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory

namespace Poincare.CurvatureIntegral

lemma neg_integral_deriv_mul_reciprocal_le
    {A : ℝ → ℝ} {a b α : ℝ} (ha : 0 < a) (hab : a ≤ b) (hα : 0 ≤ α)
    (hc : ContinuousOn A (Icc a b))
    (hd : DifferentiableOn ℝ A (Ioo a b))
    (hi : IntervalIntegrable (deriv A) volume a b)
    (hA : ∀ t ∈ Icc a b, 0 ≤ A t) :
    -(∫ t in a..b, deriv A t * (α / t)) ≤ A a * (α / a) := by
  have hu : ContinuousOn (fun t : ℝ => α / t) (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact continuousOn_const.div continuousOn_id (fun t ht => (ha.trans_le ht.1).ne')
  have hu' : ContinuousOn (fun t : ℝ => -α / t ^ 2) (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact continuousOn_const.div (continuousOn_id.pow 2)
      (fun t ht => pow_ne_zero _ (ha.trans_le ht.1).ne')
  have hc' : ContinuousOn A (uIcc a b) := by rwa [uIcc_of_le hab]
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hu hc'
    (fun t ht => by
      have ht' : t ∈ Ioo a b := by simpa only [min_eq_left hab, max_eq_right hab] using ht
      convert (hasDerivAt_const t α).div (hasDerivAt_id t) (ha.trans ht'.1).ne' using 1 <;>
        first | rfl | simp)
    (fun t ht => by
      have ht' : t ∈ Ioo a b := by simpa only [min_eq_left hab, max_eq_right hab] using ht
      exact (hd t ht').differentiableAt (isOpen_Ioo.mem_nhds ht') |>.hasDerivAt)
    hu'.intervalIntegrable hi
  have hneg : (∫ t in a..b, (-α / t ^ 2) * A t) ≤ 0 := by
    have h := intervalIntegral.integral_nonneg (μ := volume) hab
      (f := fun t => -((-α / t ^ 2) * A t))
      (fun t ht => neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg
        (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hα) (sq_nonneg t)) (hA t ht)))
    simpa only [intervalIntegral.integral_neg, neg_nonneg] using h
  have hb := mul_nonneg (div_nonneg hα (ha.trans_le hab).le) (hA b ⟨hab, le_rfl⟩)
  simp_rw [mul_comm (α / _) (deriv A _)] at hparts
  nlinarith

lemma area_mul_reciprocal_sq_le
    {A : ℝ → ℝ} {t α : ℝ} {m : ℕ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hm : 2 ≤ m) (hα : 0 ≤ α) (hA : A t ≤ α * t ^ m) :
    A t * (α / t) ^ 2 ≤ α ^ 3 := by
  have hpow : t ^ m ≤ t ^ 2 := pow_le_pow_of_le_one ht.le ht1 hm
  have hAt : A t ≤ α * t ^ 2 := hA.trans (mul_le_mul_of_nonneg_left hpow hα)
  calc
    A t * (α / t) ^ 2 ≤ (α * t ^ 2) * (α / t) ^ 2 :=
      mul_le_mul_of_nonneg_right hAt (sq_nonneg _)
    _ = α ^ 3 := by field_simp

lemma integral_area_mul_reciprocal_sq_le
    {A : ℝ → ℝ} {a b α : ℝ} {m : ℕ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 1) (hm : 2 ≤ m) (hα : 0 ≤ α)
    (hc : ContinuousOn A (Icc a b))
    (hA : ∀ t ∈ Icc a b, A t ≤ α * t ^ m) :
    (∫ t in a..b, A t * (α / t) ^ 2) ≤ α ^ 3 * (b - a) := by
  have hi : IntervalIntegrable (fun t => A t * (α / t) ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact hc.mul ((continuousOn_const.div continuousOn_id
      (fun t ht => (ha.trans_le ht.1).ne')).pow 2)
  have h := intervalIntegral.integral_mono_on hab hi intervalIntegrable_const
    (fun t ht => area_mul_reciprocal_sq_le (ha.trans_le ht.1) (ht.2.trans hb) hm hα (hA t ht))
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm (b - a)] using h

lemma neg_integral_deriv_mul_reciprocal_le_of_power_bound
    {A : ℝ → ℝ} {a b α : ℝ} {m : ℕ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 1) (hm : 1 ≤ m) (hα : 0 ≤ α)
    (hc : ContinuousOn A (Icc a b))
    (hd : DifferentiableOn ℝ A (Ioo a b))
    (hi : IntervalIntegrable (deriv A) volume a b)
    (hA : ∀ t ∈ Icc a b, 0 ≤ A t)
    (hleft : A a ≤ α * a ^ m) :
    -(∫ t in a..b, deriv A t * (α / t)) ≤ α ^ 2 := by
  have hpow : a ^ m ≤ a := by
    simpa only [pow_one] using pow_le_pow_of_le_one ha.le (hab.trans hb) hm
  calc
    -(∫ t in a..b, deriv A t * (α / t)) ≤ A a * (α / a) :=
      neg_integral_deriv_mul_reciprocal_le ha hab hα hc hd hi hA
    _ ≤ (α * a) * (α / a) := mul_le_mul_of_nonneg_right
      (hleft.trans (mul_le_mul_of_nonneg_left hpow hα)) (div_nonneg hα ha.le)
    _ = α ^ 2 := by field_simp

lemma area_error_le_of_power_bound
    {A : ℝ → ℝ} {a b α : ℝ} {m : ℕ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 1) (hm : 2 ≤ m) (hα : 0 ≤ α)
    (hc : ContinuousOn A (Icc a b))
    (hd : DifferentiableOn ℝ A (Ioo a b))
    (hi : IntervalIntegrable (deriv A) volume a b)
    (hA : ∀ t ∈ Icc a b, 0 ≤ A t ∧ A t ≤ α * t ^ m) :
    (b - a) + m * (1 + α) * (∫ t in a..b, A t * (α / t) ^ 2) -
      (∫ t in a..b, deriv A t * (α / t)) ≤
        1 + m * (1 + α) * α ^ 3 + α ^ 2 := by
  have harea := integral_area_mul_reciprocal_sq_le ha hab hb hm hα hc
    (fun t ht => (hA t ht).2)
  have hderiv := neg_integral_deriv_mul_reciprocal_le_of_power_bound
    ha hab hb (by omega : 1 ≤ m) hα hc hd hi
    (fun t ht => (hA t ht).1) (hA a ⟨le_rfl, hab⟩).2
  have hlen : b - a ≤ 1 := by linarith
  have harea' : (∫ t in a..b, A t * (α / t) ^ 2) ≤ α ^ 3 :=
    harea.trans (by nlinarith [pow_nonneg hα 3])
  have hcoef : 0 ≤ (m : ℝ) * (1 + α) := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have hmul := mul_le_mul_of_nonneg_left harea' hcoef
  linarith

lemma le_mul_one_add_of_forall_le_sub_deriv
    {A : ℝ → ℝ} {b α C K S : ℝ} {m : ℕ}
    (hb : 0 < b) (hb1 : b ≤ 1) (hm : 1 ≤ m) (hα : 0 ≤ α) (hK : 0 ≤ K)
    (hc : ContinuousOn A (Icc b (3 * b / 2)))
    (hd : DifferentiableOn ℝ A (Ioo b (3 * b / 2)))
    (hleft : A b ≤ α * b ^ m) (hright : 0 ≤ A (3 * b / 2))
    (hS : ∀ t ∈ Ioo b (3 * b / 2), S ≤ C * (1 + K) - deriv A t) :
    S ≤ (C + 2 * α) * (1 + K) := by
  obtain ⟨t, ht, hderiv⟩ := Poincare.Analysis.exists_neg_deriv_le_of_power_bound
    hb hm hc hd hleft hright
  have hp : b ^ (m - 1) ≤ 1 := pow_le_one₀ hb.le hb1
  have hscale : 2 * α * b ^ (m - 1) ≤ 2 * α := by nlinarith
  have h := hS t ht
  nlinarith [mul_nonneg hα hK]

end Poincare.CurvatureIntegral
