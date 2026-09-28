import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_13_BarrierConstants
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false

open Set MeasureTheory
open scoped intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

theorem capScalarIntegral_eq {c a theta : ℝ} (ha : a < 1) (htheta : theta < 1) :
    (∫ t in a..theta, c / (2 * (1 - t))) =
      (c / 2) * (Real.log (1 - a) - Real.log (1 - theta)) := by
  have hform : (fun t : ℝ => c / (2 * (1 - t))) =
      fun t => (c / 2) * (1 - t)⁻¹ := by
    funext t
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hform, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_left (fun t : ℝ => t⁻¹) 1,
    integral_inv_of_pos (sub_pos.mpr htheta) (sub_pos.mpr ha),
    Real.log_div (sub_pos.mpr ha).ne' (sub_pos.mpr htheta).ne']

theorem capScalarIntegral_lower {c a theta : ℝ} (hc : 0 ≤ c)
    (ha : a ≤ 1 / 2) (htheta : theta < 1) :
    -(c / 2) * (Real.log (1 - theta) + Real.log 2) ≤
      ∫ t in a..theta, c / (2 * (1 - t)) := by
  have haOne : a < 1 := by linarith
  rw [capScalarIntegral_eq haOne htheta]
  have hlog : -Real.log 2 ≤ Real.log (1 - a) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2)
      (by linarith : (1 / 2 : ℝ) ≤ 1 - a)
    simpa only [one_div, Real.log_inv] using h
  have hmul := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ c / 2)
  linarith

theorem capTopAction_gt {c ell theta a : ℝ} (hc : 0 < c)
    (htheta : 1 / 2 < theta) (hthetaOne : theta < 1)
    (hbudget : ell < -(c / 2) * (Real.log (1 - theta) + Real.log 2))
    (ha : a ≤ 1 / 2) (density : ℝ → ℝ)
    (hint : IntervalIntegrable density volume a theta)
    (hscalar : ∀ t ∈ Ioo a theta, c / (2 * (1 - t)) ≤ density t) :
    ell < ∫ t in a..theta, density t := by
  have haTheta : a ≤ theta := ha.trans htheta.le
  have hbarrier : IntervalIntegrable (fun t : ℝ => c / (2 * (1 - t)))
      volume a theta := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le haTheta]
    apply continuousOn_const.div (continuousOn_const.mul
      (continuousOn_const.sub continuousOn_id))
    intro t ht
    have : 0 < 2 * (1 - t) := by linarith [ht.2]
    exact this.ne'
  exact (hbudget.trans_le (capScalarIntegral_lower hc.le ha hthetaOne)).trans_le
    (intervalIntegral.integral_mono_on_of_le_Ioo haTheta hbarrier hint hscalar)

theorem exists_standardCapTopAction {g0 : StandardInitialMetric}
    (P : RepairedCapPersistenceData.{u} g0) (ell : ℝ) :
    ∃ theta : ℝ, 1 / 2 < theta ∧ theta < 1 ∧
      ∀ (a : ℝ), 0 ≤ a → a ≤ 1 / 2 →
      ∀ gamma : ℝ → StandardCapSpace,
      ∀ kinetic : ℝ → ℝ, (∀ t ∈ Ioo a theta, 0 ≤ kinetic t) →
      IntervalIntegrable
        (fun t => (P.standard_cap.flow.connection t).scalarCurvature (gamma t) + kinetic t)
        volume a theta →
      ell < ∫ t in a..theta,
        (P.standard_cap.flow.connection t).scalarCurvature (gamma t) + kinetic t := by
  obtain ⟨c, hc, hscalar⟩ := P.standardScalarRate
  obtain ⟨theta, htheta, hthetaOne, hbudget⟩ := exists_capTopBarrierTime c hc ell
  refine ⟨theta, htheta, hthetaOne, ?_⟩
  intro a ha haHalf gamma kinetic hkinetic hint
  apply capTopAction_gt hc htheta hthetaOne hbudget haHalf _ hint
  intro t ht
  have htFlow : t ∈ Ico 0 P.standard_cap.flow.base.lifetime := by
    rw [P.standard_cap.lifetime_one]
    exact ⟨ha.trans ht.1.le, ht.2.trans hthetaOne⟩
  have hhalf : c / (2 * (1 - t)) ≤ c / (1 - t) := by
    have hpos : 0 < 1 - t := sub_pos.mpr (ht.2.trans hthetaOne)
    apply (div_le_div_iff₀ (mul_pos (by norm_num) hpos) hpos).mpr
    nlinarith
  exact hhalf.trans ((hscalar t htFlow (gamma t)).trans
    (le_add_of_nonneg_right (hkinetic t ht)))

end PoincareConjecture.Proofs.M46
