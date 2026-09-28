import PoincareConjecture.Proofs.M36.CollapseMetric

set_option autoImplicit false

namespace PoincareConjecture.M36

theorem flat_exponential_le_one (x : ℝ) : expNegInvGlue x ≤ 1 := by
  by_cases hx : x ≤ 0
  · simp [expNegInvGlue, hx]
  · rw [expNegInvGlue, if_neg hx]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (inv_nonneg.mpr (le_of_not_ge hx)))

theorem smoothProfile_le {C epsilon : ℝ} (hC : 0 ≤ C) (hepsilon : 0 ≤ epsilon)
    (q s : ℝ) : smoothProfile C q epsilon s ≤ C * epsilon := by
  unfold smoothProfile
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (flat_exponential_le_one (s / q)) (mul_nonneg hC hepsilon)

theorem conformalFactor_ge_exp {C epsilon : ℝ} (hC : 0 ≤ C) (hepsilon : 0 ≤ epsilon)
    (q s : ℝ) : Real.exp (-2 * C * epsilon) ≤ conformalFactor C q epsilon s := by
  unfold conformalFactor
  apply Real.exp_le_exp.mpr
  linarith [smoothProfile_le hC hepsilon q s]

theorem radialConformalMultiplier_ge_exp (g₀ : StandardInitialMetric)
    {C epsilon : ℝ} (hC : 0 ≤ C) (hepsilon : 0 ≤ epsilon)
    (q r : ℝ) (x : StandardCapSpace) :
    Real.exp (-2 * C * epsilon) ≤ radialConformalMultiplier g₀ C q epsilon r x := by
  have hb := radialTipWeight_bounds g₀ r x
  have hn := mul_le_mul_of_nonneg_left
    (conformalFactor_ge_exp hC hepsilon q (standardSurgeryHeight g₀ x)) hb.1
  have ht := mul_le_mul_of_nonneg_left
    (conformalFactor_ge_exp hC hepsilon q (g₀.cylindrical_end.radius + 4))
    (sub_nonneg.mpr hb.2)
  unfold radialConformalMultiplier
  calc
    _ = radialTipWeight g₀ r x * Real.exp (-2 * C * epsilon) +
        (1 - radialTipWeight g₀ r x) * Real.exp (-2 * C * epsilon) := by ring
    _ ≤ _ := add_le_add hn ht

theorem surgery_ball_factor_margins {A C epsilon : ℝ}
    (hA : 1 < A) (hC : 0 ≤ C) (hepsilon : 0 ≤ epsilon)
    (heta : 0 < 1 - 6 * epsilon)
    (hsmall : epsilon ≤ 1 / (A * (6 + 2 * C))) :
    A - 1 < Real.sqrt ((1 - 6 * epsilon) * Real.exp (-2 * C * epsilon)) * A ∧
      Real.sqrt (1 + 6 * epsilon) * A < A + 1 := by
  have hApos : 0 < A := by linarith
  have hDpos : 0 < 6 + 2 * C := by linarith
  have hproduct : epsilon * (A * (6 + 2 * C)) ≤ 1 :=
    (le_div_iff₀ (mul_pos hApos hDpos)).mp hsmall
  have hexp := Real.add_one_le_exp (-2 * C * epsilon)
  have hbeta : 1 - (6 + 2 * C) * epsilon ≤
      (1 - 6 * epsilon) * Real.exp (-2 * C * epsilon) := by
    have h := mul_le_mul_of_nonneg_left hexp heta.le
    have hcross : 0 ≤ C * epsilon ^ 2 := mul_nonneg hC (sq_nonneg epsilon)
    nlinarith
  have hbetapos := mul_pos heta (Real.exp_pos (-2 * C * epsilon))
  have htim := mul_le_mul_of_nonneg_right hproduct hApos.le
  have hbetatim := mul_le_mul_of_nonneg_right hbeta (sq_nonneg A)
  have hbetasq : (A - 1) ^ 2 <
      ((1 - 6 * epsilon) * Real.exp (-2 * C * epsilon)) * A ^ 2 := by
    nlinarith
  have hsix : 6 * epsilon * A ≤ 1 := by
    have hcross : 0 ≤ 2 * C * epsilon * A := by positivity
    nlinarith
  have hsixtim := mul_le_mul_of_nonneg_right hsix hApos.le
  have hupsq : (1 + 6 * epsilon) * A ^ 2 < (A + 1) ^ 2 := by nlinarith
  constructor
  · have hsquare :
        (Real.sqrt ((1 - 6 * epsilon) * Real.exp (-2 * C * epsilon)) * A) ^ 2 =
          ((1 - 6 * epsilon) * Real.exp (-2 * C * epsilon)) * A ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hbetapos.le]
    have hnonneg := mul_nonneg
      (Real.sqrt_nonneg ((1 - 6 * epsilon) * Real.exp (-2 * C * epsilon))) hApos.le
    nlinarith
  · have hsquare : (Real.sqrt (1 + 6 * epsilon) * A) ^ 2 = (1 + 6 * epsilon) * A ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    have hnonneg := mul_nonneg (Real.sqrt_nonneg (1 + 6 * epsilon)) hApos.le
    nlinarith

end PoincareConjecture.M36
