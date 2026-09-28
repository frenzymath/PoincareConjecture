import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic









set_option autoImplicit false

open MeasureTheory
open scoped intervalIntegral

namespace MeasureTheory



theorem integral_mul_weight_sq_le {X : Type*} [MeasurableSpace X]
    {mu : Measure X} {f w : X → ℝ} (hw : 0 ≤ᵐ[mu] w)
    (hiw : Integrable w mu) (hifw : Integrable (fun x => f x * w x) mu)
    (hif2w : Integrable (fun x => (f x) ^ 2 * w x) mu) :
    (∫ x, f x * w x ∂mu) ^ 2 ≤ (∫ x, w x ∂mu) * (∫ x, (f x) ^ 2 * w x ∂mu) := by
  have hquad (r : ℝ) :
      0 ≤ (∫ x, w x ∂mu) * (r * r) +
        (-2 * ∫ x, f x * w x ∂mu) * r + ∫ x, (f x) ^ 2 * w x ∂mu := by
    have hn : 0 ≤ ∫ x, (r - f x) ^ 2 * w x ∂mu :=
      integral_nonneg_of_ae (hw.mono fun x hx => mul_nonneg (sq_nonneg _) hx)
    have heq : (fun x => (r - f x) ^ 2 * w x) =
        fun x => (r * r) * w x + (-2 * r) * (f x * w x) + (f x) ^ 2 * w x := by
      funext x
      ring
    have hsum : Integrable (fun x => (r * r) * w x + (-2 * r) * (f x * w x)) mu :=
      (hiw.const_mul (r * r)).add (hifw.const_mul (-2 * r))
    rw [heq, integral_add hsum hif2w,
      integral_add (hiw.const_mul (r * r)) (hifw.const_mul (-2 * r)),
      integral_const_mul, integral_const_mul] at hn
    nlinarith only [hn]
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  nlinarith only [hd]

end MeasureTheory

namespace intervalIntegral



theorem integral_mul_weight_sq_le {f w : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hw : ∀ x, 0 ≤ w x)
    (hiw : IntervalIntegrable w volume a b)
    (hifw : IntervalIntegrable (fun x => f x * w x) volume a b)
    (hif2w : IntervalIntegrable (fun x => (f x) ^ 2 * w x) volume a b) :
    (∫ x in a..b, f x * w x) ^ 2 ≤
      (∫ x in a..b, w x) * (∫ x in a..b, (f x) ^ 2 * w x) := by
  simp only [integral_of_le hab]
  exact MeasureTheory.integral_mul_weight_sq_le (Filter.Eventually.of_forall hw)
    hiw.1 hifw.1 hif2w.1

end intervalIntegral
