import PoincareConjecture.Definitions.M14GeneralizedLGeometry
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false

open Set MeasureTheory
open scoped intervalIntegral

namespace PoincareConjecture.Proofs.M46

theorem integral_sqrt_nonneg_endpoint {tau : ℝ} (htau : 0 ≤ tau) :
    (∫ s in (0 : ℝ)..tau, Real.sqrt s) = (2 / 3 : ℝ) * tau * Real.sqrt tau := by
  obtain rfl | htau := htau.eq_or_lt
  · simp
  simp_rw [Real.sqrt_eq_rpow]
  rw [integral_rpow (Or.inl (by norm_num)), Real.rpow_add htau]
  norm_num
  ring

theorem positiveAction_le_action_add {R kinetic : ℝ → ℝ} {tau K : ℝ}
    (htau : 0 ≤ tau) (hK : 0 ≤ K)
    (hscalar : ∀ s ∈ Ioo 0 tau, -K ≤ R s)
    (hactual : IntervalIntegrable
      (fun s => Real.sqrt s * (R s + kinetic s)) volume 0 tau)
    (hpositive : IntervalIntegrable
      (fun s => Real.sqrt s * (max (R s) 0 + kinetic s)) volume 0 tau) :
    (∫ s in (0 : ℝ)..tau, Real.sqrt s * (max (R s) 0 + kinetic s)) ≤
      (∫ s in (0 : ℝ)..tau, Real.sqrt s * (R s + kinetic s)) +
        (2 / 3 : ℝ) * K * tau * Real.sqrt tau := by
  have hcorrection : IntervalIntegrable (fun s : ℝ => K * Real.sqrt s)
      volume 0 tau := (Real.continuous_sqrt.const_mul K).intervalIntegrable 0 tau
  have hbound := intervalIntegral.integral_mono_on_of_le_Ioo htau
    hpositive (hactual.add hcorrection) (fun s hs => show
      Real.sqrt s * (max (R s) 0 + kinetic s) ≤
        Real.sqrt s * (R s + kinetic s) + K * Real.sqrt s from by
      have hm : max (R s) 0 ≤ R s + K := max_le (by linarith) (by linarith [hscalar s hs])
      have hmul := mul_le_mul_of_nonneg_left hm (Real.sqrt_nonneg s)
      nlinarith)
  rw [intervalIntegral.integral_add hactual hcorrection,
    intervalIntegral.integral_const_mul, integral_sqrt_nonneg_endpoint htau] at hbound
  convert hbound using 1
  ring

theorem weightedAction_ge_tail {density : ℝ → ℝ} {a b tau : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbtau : b ≤ tau)
    (hnonneg : ∀ s, 0 ≤ density s)
    (hweighted : IntervalIntegrable (fun s => Real.sqrt s * density s) volume 0 tau)
    (htail : IntervalIntegrable density volume a b) :
    Real.sqrt a * (∫ s in a..b, density s) ≤
      ∫ s in (0 : ℝ)..tau, Real.sqrt s * density s := by
  have hsub : uIcc a b ⊆ uIcc 0 tau := by
    rw [uIcc_of_le hab, uIcc_of_le (ha.trans (hab.trans hbtau))]
    exact Icc_subset_Icc ha hbtau
  have hlocal := intervalIntegral.integral_mono_on hab
    (htail.const_mul (Real.sqrt a)) (hweighted.mono_set hsub)
    (fun s hs => mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hs.1) (hnonneg s))
  rw [intervalIntegral.integral_const_mul] at hlocal
  exact hlocal.trans (intervalIntegral.integral_mono_interval ha hab hbtau
    (Filter.Eventually.of_forall (fun s => mul_nonneg (Real.sqrt_nonneg s) (hnonneg s)))
    hweighted)

theorem weightedAction_gt_of_tail {density : ℝ → ℝ} {a b tau budget : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hbtau : b ≤ tau)
    (hnonneg : ∀ s, 0 ≤ density s)
    (hweighted : IntervalIntegrable (fun s => Real.sqrt s * density s) volume 0 tau)
    (htail : IntervalIntegrable density volume a b)
    (hentry : budget / Real.sqrt a < ∫ s in a..b, density s) :
    budget < ∫ s in (0 : ℝ)..tau, Real.sqrt s * density s := by
  have hroot : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hbudget : budget < Real.sqrt a * (∫ s in a..b, density s) := by
    have h := (div_lt_iff₀ hroot).mp hentry
    simpa only [mul_comm] using h
  exact hbudget.trans_le (weightedAction_ge_tail ha.le hab hbtau hnonneg hweighted htail)

end PoincareConjecture.Proofs.M46
