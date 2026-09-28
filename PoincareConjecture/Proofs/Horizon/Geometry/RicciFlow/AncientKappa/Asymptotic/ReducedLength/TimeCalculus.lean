import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Tactic









set_option autoImplicit false

open Set Filter MeasureTheory
open scoped intervalIntegral

namespace PoincareConjecture



theorem weighted_time_le_of_deriv_lower {f : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hderiv : ∀ᵐ t ∂volume.restrict (Ioo a b), -2 * f t / t ≤ deriv f t) :
    f a * a ^ 2 ≤ f b * b ^ 2 := by
  have hid : AbsolutelyContinuousOnInterval (fun t : ℝ => t) a b :=
    LipschitzWith.id.lipschitzOnWith.absolutelyContinuousOnInterval
  have hsquare : AbsolutelyContinuousOnInterval (fun t : ℝ => t ^ 2) a b := by
    simpa only [pow_two] using hid.fun_mul hid
  have hnonneg : 0 ≤ᵐ[volume.restrict (Icc a b)]
      (fun t => deriv f t * t ^ 2 + f t * deriv (fun s : ℝ => s ^ 2) t) := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [hderiv, ae_restrict_mem measurableSet_Ioo] with t ht htab
    have htpos : 0 < t := ha.trans htab.1
    have hmul := mul_le_mul_of_nonneg_right ht (sq_nonneg t)
    have hcancel : (-2 * f t / t) * t ^ 2 = -2 * f t * t := by
      field_simp [htpos.ne']
    rw [hcancel] at hmul
    rw [show deriv (fun s : ℝ => s ^ 2) t = 2 * t by
      simp]
    simp only [Pi.zero_apply]
    nlinarith
  have hi := intervalIntegral.integral_nonneg_of_ae_restrict hab hnonneg
  rw [hf.integral_deriv_mul_eq_sub hsquare] at hi
  linarith

end PoincareConjecture
