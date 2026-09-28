import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring










set_option autoImplicit false

open Set MeasureTheory
open scoped intervalIntegral

namespace PoincareConjecture.ReducedLengthMinimum.Variation





theorem sq_mul_integral_trace_eq {c : ℝ} (hc : 0 < c)
    (R V S G C D : ℝ → ℝ)
    (hRc : ContinuousOn R (Icc 0 c)) (hVc : ContinuousOn V (Icc 0 c))
    (hR : ∀ s ∈ Ioo 0 c, HasDerivAt R (-2 * s * S s + G s) s)
    (hV : ∀ s ∈ Ioo 0 c, HasDerivAt V (-4 * s * C s + 4 * s ^ 2 * G s) s)
    (hD : IntervalIntegrable D volume 0 c)
    (htrace : ∀ s ∈ Ioo 0 c,
      c ^ 2 * D s = 2 - 4 * s ^ 2 * R s + 2 * s ^ 4 * S s - s ^ 2 * C s) :
    c ^ 2 * (∫ s in 0..c, D s) =
      2 * c - c ^ 3 * R c + c * V c / 4 -
        (∫ s in 0..c, V s / 2 + 2 * s ^ 2 * R s) / 2 := by
  let A : ℝ → ℝ := fun s => V s / 2 + 2 * s ^ 2 * R s
  let Q : ℝ → ℝ := fun s => -(s ^ 3 * R s) + s * V s / 4
  have hAc : ContinuousOn A (Icc 0 c) :=
    (hVc.div_const 2).add ((continuousOn_const.mul (continuousOn_id.pow 2)).mul hRc)
  have hQc : ContinuousOn Q (Icc 0 c) :=
    ((continuousOn_id.pow 3).mul hRc).neg.add ((continuousOn_id.mul hVc).div_const 4)
  have hAi : IntervalIntegrable A volume 0 c := hAc.intervalIntegrable_of_Icc hc.le
  have hQi : IntervalIntegrable (fun s => c ^ 2 * D s - 2 + A s / 2) volume 0 c :=
    ((hD.const_mul _).sub intervalIntegrable_const).add (hAi.div_const 2)
  have hQd (s : ℝ) (hs : s ∈ Ioo 0 c) :
      HasDerivAt Q (c ^ 2 * D s - 2 + A s / 2) s := by
    have h := (((hasDerivAt_pow 3 s).mul (hR s hs)).neg).add
      (((hasDerivAt_id s).mul (hV s hs)).div_const 4)
    apply h.congr_deriv
    rw [htrace s hs]
    dsimp only [A]
    norm_num only [Nat.cast_ofNat, Nat.reduceSub, one_mul, id_eq]
    ring
  have hFTC : (∫ s in 0..c, c ^ 2 * D s - 2 + A s / 2) = Q c - Q 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hc.le hQc hQd hQi
  rw [intervalIntegral.integral_add ((hD.const_mul _).sub intervalIntegrable_const)
      (hAi.div_const 2),
    intervalIntegral.integral_sub (hD.const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
    intervalIntegral.integral_div] at hFTC
  simp only [Q, zero_pow (by norm_num : (3 : ℕ) ≠ 0), zero_mul, zero_div,
    neg_zero, add_zero, sub_zero, smul_eq_mul] at hFTC
  change c ^ 2 * (∫ s in 0..c, D s) =
    2 * c - c ^ 3 * R c + c * V c / 4 - (∫ s in 0..c, A s) / 2
  linarith



theorem curvature_add_minimum_le_two {c τ m : ℝ} (hc : 0 < c) (hτ : τ = c ^ 2)
    (R V S G C D : ℝ → ℝ)
    (hRc : ContinuousOn R (Icc 0 c)) (hVc : ContinuousOn V (Icc 0 c))
    (hR : ∀ s ∈ Ioo 0 c, HasDerivAt R (-2 * s * S s + G s) s)
    (hV : ∀ s ∈ Ioo 0 c, HasDerivAt V (-4 * s * C s + 4 * s ^ 2 * G s) s)
    (hD : IntervalIntegrable D volume 0 c)
    (htrace : ∀ s ∈ Ioo 0 c,
      c ^ 2 * D s = 2 - 4 * s ^ 2 * R s + 2 * s ^ 4 * S s - s ^ 2 * C s)
    (hterminal : V c = 0)
    (haction : (∫ s in 0..c, V s / 2 + 2 * s ^ 2 * R s) = 2 * c * m)
    (hindex : 0 ≤ ∫ s in 0..c, D s) :
    τ * R c + m ≤ 2 := by
  have hid := sq_mul_integral_trace_eq hc R V S G C D hRc hVc hR hV hD htrace
  rw [hterminal, haction] at hid
  have hscaled : 0 ≤ c * (2 - c ^ 2 * R c - m) := by
    have hnonneg := mul_nonneg (sq_nonneg c) hindex
    nlinarith only [hid, hnonneg]
  have hbound := nonneg_of_mul_nonneg_right hscaled hc
  rw [hτ]
  linarith

end PoincareConjecture.ReducedLengthMinimum.Variation
