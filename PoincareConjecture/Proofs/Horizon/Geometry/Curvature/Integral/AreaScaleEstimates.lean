import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.AreaEstimates









set_option autoImplicit false

open Set MeasureTheory

namespace Poincare.CurvatureIntegral

lemma area_mul_reciprocal_sq_le_pow
    {A : ℝ → ℝ} {t α : ℝ} {m : ℕ} (ht : 0 < t)
    (hm : 2 ≤ m) (hA : A t ≤ α * t ^ m) :
    A t * (α / t) ^ 2 ≤ α ^ 3 * t ^ (m - 2) := by
  calc
    A t * (α / t) ^ 2 ≤ (α * t ^ m) * (α / t) ^ 2 :=
      mul_le_mul_of_nonneg_right hA (sq_nonneg _)
    _ = α ^ 3 * t ^ (m - 2) := by
      have heq : m = (m - 2) + 2 := by omega
      conv_lhs => rw [heq, pow_add]
      field_simp

lemma integral_area_mul_reciprocal_sq_le_pow
    {A : ℝ → ℝ} {a b α : ℝ} {m : ℕ} (ha : 0 < a) (hab : a ≤ b)
    (hm : 2 ≤ m) (hα : 0 ≤ α)
    (hc : ContinuousOn A (Icc a b))
    (hA : ∀ t ∈ Icc a b, A t ≤ α * t ^ m) :
    (∫ t in a..b, A t * (α / t) ^ 2) ≤ α ^ 3 * b ^ (m - 2) * (b - a) := by
  have hi : IntervalIntegrable (fun t => A t * (α / t) ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact hc.mul ((continuousOn_const.div continuousOn_id
      (fun t ht => (ha.trans_le ht.1).ne')).pow 2)
  have h := intervalIntegral.integral_mono_on hab hi intervalIntegrable_const
    (fun t ht => (area_mul_reciprocal_sq_le_pow (ha.trans_le ht.1) hm (hA t ht)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (ha.trans_le ht.1).le ht.2 _)
        (pow_nonneg hα 3)))
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm (b - a)] using h

lemma area_mul_reciprocal_le_pow
    {A : ℝ → ℝ} {t α : ℝ} {m : ℕ} (ht : 0 < t)
    (hm : 1 ≤ m) (hα : 0 ≤ α) (hA : A t ≤ α * t ^ m) :
    A t * (α / t) ≤ α ^ 2 * t ^ (m - 1) := by
  calc
    A t * (α / t) ≤ (α * t ^ m) * (α / t) :=
      mul_le_mul_of_nonneg_right hA (div_nonneg hα ht.le)
    _ = α ^ 2 * t ^ (m - 1) := by
      have heq : m = (m - 1) + 1 := by omega
      conv_lhs => rw [heq, pow_add, pow_one]
      field_simp

lemma neg_integral_deriv_mul_reciprocal_le_pow
    {A : ℝ → ℝ} {a b α : ℝ} {m : ℕ} (ha : 0 < a) (hab : a ≤ b)
    (hm : 1 ≤ m) (hα : 0 ≤ α)
    (hc : ContinuousOn A (Icc a b))
    (hd : DifferentiableOn ℝ A (Ioo a b))
    (hi : IntervalIntegrable (deriv A) volume a b)
    (hA : ∀ t ∈ Icc a b, 0 ≤ A t) (hleft : A a ≤ α * a ^ m) :
    -(∫ t in a..b, deriv A t * (α / t)) ≤ α ^ 2 * b ^ (m - 1) := by
  calc
    -(∫ t in a..b, deriv A t * (α / t)) ≤ A a * (α / a) :=
      neg_integral_deriv_mul_reciprocal_le ha hab hα hc hd hi hA
    _ ≤ α ^ 2 * a ^ (m - 1) := area_mul_reciprocal_le_pow ha hm hα hleft
    _ ≤ α ^ 2 * b ^ (m - 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le hab _) (sq_nonneg α)



lemma area_error_le_mul_pow
    {A : ℝ → ℝ} {a b α : ℝ} {m : ℕ} (ha : 0 < a) (hab : a ≤ b)
    (hm : 2 ≤ m) (hα : 0 ≤ α)
    (hc : ContinuousOn A (Icc a b))
    (hd : DifferentiableOn ℝ A (Ioo a b))
    (hi : IntervalIntegrable (deriv A) volume a b)
    (hA : ∀ t ∈ Icc a b, 0 ≤ A t ∧ A t ≤ α * t ^ m) :
    m * (1 + α) * (∫ t in a..b, A t * (α / t) ^ 2) -
      (∫ t in a..b, deriv A t * (α / t)) ≤
        (m * (1 + α) * α ^ 3 + α ^ 2) * b ^ (m - 1) := by
  have harea := integral_area_mul_reciprocal_sq_le_pow ha hab hm hα hc
    (fun t ht => (hA t ht).2)
  have hderiv := neg_integral_deriv_mul_reciprocal_le_pow ha hab (by omega : 1 ≤ m)
    hα hc hd hi (fun t ht => (hA t ht).1) (hA a ⟨le_rfl, hab⟩).2
  have hscale : b ^ (m - 2) * (b - a) ≤ b ^ (m - 1) := by
    have heq : m - 1 = (m - 2) + 1 := by omega
    rw [heq, pow_succ]
    exact mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg (ha.trans_le hab).le _)
  have harea' : (∫ t in a..b, A t * (α / t) ^ 2) ≤ α ^ 3 * b ^ (m - 1) :=
    harea.trans (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hscale (pow_nonneg hα 3))
  have hcoef : 0 ≤ (m : ℝ) * (1 + α) := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have hmul := mul_le_mul_of_nonneg_left harea' hcoef
  nlinarith only [hmul, hderiv]

lemma le_add_mul_pow_of_forall_le_sub_deriv
    {A : ℝ → ℝ} {b α T S : ℝ} {m : ℕ}
    (hb : 0 < b) (hm : 1 ≤ m)
    (hc : ContinuousOn A (Icc b (3 * b / 2)))
    (hd : DifferentiableOn ℝ A (Ioo b (3 * b / 2)))
    (hleft : A b ≤ α * b ^ m) (hright : 0 ≤ A (3 * b / 2))
    (hS : ∀ t ∈ Ioo b (3 * b / 2), S ≤ T - deriv A t) :
    S ≤ T + 2 * α * b ^ (m - 1) := by
  obtain ⟨t, ht, hderiv⟩ := Poincare.Analysis.exists_neg_deriv_le_of_power_bound
    hb hm hc hd hleft hright
  linarith [hS t ht]

end Poincare.CurvatureIntegral
