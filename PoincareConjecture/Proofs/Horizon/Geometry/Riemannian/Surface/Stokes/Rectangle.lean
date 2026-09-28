import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.ContDiff.Basic

set_option autoImplicit false

open Set MeasureTheory
open scoped Interval

namespace PoincareConjecture.Surface

theorem integral_curl_rectangle
    (P Q : ℝ × ℝ → ℝ)
    (hP : ContDiff ℝ 1 P) (hQ : ContDiff ℝ 1 Q)
    {a₁ a₂ b₁ b₂ : ℝ} (ha₁ : a₁ ≤ b₁) (ha₂ : a₂ ≤ b₂) :
    (∫ x in a₁..b₁, ∫ y in a₂..b₂,
      fderiv ℝ Q (x, y) (1, 0) - fderiv ℝ P (x, y) (0, 1)) =
      ((∫ x in a₁..b₁, P (x, a₂)) - ∫ x in a₁..b₁, P (x, b₂)) +
        (∫ y in a₂..b₂, Q (b₁, y)) - ∫ y in a₂..b₂, Q (a₁, y) := by
  have hR : IsCompact (Icc (a₁, a₂) (b₁, b₂)) := isCompact_Icc
  have hcont : ContinuousOn
      (fun x : ℝ × ℝ => fderiv ℝ Q x (1, 0) - fderiv ℝ P x (0, 1))
        (Icc (a₁, a₂) (b₁, b₂)) := by
    exact ((hQ.continuous_fderiv one_ne_zero).clm_apply continuous_const).sub
      ((hP.continuous_fderiv one_ne_zero).clm_apply continuous_const) |>.continuousOn
  have hi : IntegrableOn
      (fun x : ℝ × ℝ => fderiv ℝ Q x (1, 0) - fderiv ℝ P x (0, 1))
        (Icc (a₁, a₂) (b₁, b₂)) :=
    hcont.integrableOn_compact hR
  have h := MeasureTheory.integral2_divergence_prod_of_hasFDerivAt
    Q (fun x => -P x) (fderiv ℝ Q) (fun x => -(fderiv ℝ P x))
    a₁ a₂ b₁ b₂ hQ.continuous.continuousOn hP.continuous.neg.continuousOn
    (fun x _ => (hQ.differentiable one_ne_zero x).hasFDerivAt)
    (fun x _ => (hP.differentiable one_ne_zero x).hasFDerivAt.neg) (by
      simpa only [uIcc_of_le ha₁, uIcc_of_le ha₂, Icc_prod_Icc,
        neg_apply, ← sub_eq_add_neg] using hi)
  simpa only [neg_apply, ← sub_eq_add_neg, intervalIntegral.integral_neg,
    neg_sub_neg] using h

end PoincareConjecture.Surface
