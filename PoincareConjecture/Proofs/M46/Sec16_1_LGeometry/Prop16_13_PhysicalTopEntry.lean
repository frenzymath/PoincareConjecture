import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_13_TopAction
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Lemma16_15_ActualPositiveAction










set_option autoImplicit false

open Set MeasureTheory
open scoped intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46




theorem capPhysicalScalarIntegral_eq {c offset q a b : ℝ} (hq : q ≠ 0) :
    (∫ t in a..b, c / (2 * (1 - (offset - t) / q) * q)) =
      ∫ s in (offset - b) / q..(offset - a) / q, c / (2 * (1 - s)) := by
  have hform : (fun t : ℝ => c / (2 * (1 - (offset - t) / q) * q)) =
      fun t => (c / (2 * (1 - (offset / q - t / q)))) / q := by
    funext t
    rw [sub_div, div_mul_eq_div_div]
  rw [hform, intervalIntegral.integral_div,
    intervalIntegral.integral_comp_sub_div (fun s : ℝ => c / (2 * (1 - s))) hq]
  simp only [smul_eq_mul, ← sub_div]
  exact mul_div_cancel_left₀ _ hq




theorem capPhysicalTopAction_gt {c ell theta offset q a b : ℝ}
    (hc : 0 < c) (hthetaOne : theta < 1)
    (hbudget : ell < -(c / 2) * (Real.log (1 - theta) + Real.log 2))
    (hq : 0 < q) (hab : a ≤ b) (htop : (offset - a) / q = theta)
    (hinner : (offset - b) / q ≤ 1 / 2)
    (density : ℝ → ℝ) (hint : IntervalIntegrable density volume a b)
    (hscalar : ∀ t ∈ Ioo a b,
      c / (2 * (1 - (offset - t) / q) * q) ≤ density t) :
    ell < ∫ t in a..b, density t := by
  have hbarrier : IntervalIntegrable
      (fun t : ℝ => c / (2 * (1 - (offset - t) / q) * q)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    apply continuousOn_const.div
      ((continuousOn_const.mul
        (continuousOn_const.sub
          ((continuousOn_const.sub continuousOn_id).div_const q))).mul continuousOn_const)
    intro t ht
    have hclock : (offset - t) / q ≤ theta := by
      rw [← htop]
      exact div_le_div_of_nonneg_right (by linarith [ht.1]) hq.le
    have : 0 < 2 * (1 - (offset - t) / q) * q := by
      exact mul_pos (mul_pos (by norm_num) (by linarith)) hq
    exact this.ne'
  have hnormalized := capScalarIntegral_lower hc.le hinner hthetaOne
  have hphysical : ell <
      ∫ t in a..b, c / (2 * (1 - (offset - t) / q) * q) := by
    rw [capPhysicalScalarIntegral_eq hq.ne', htop]
    exact hbudget.trans_le hnormalized
  exact hphysical.trans_le
    (intervalIntegral.integral_mono_on_of_le_Ioo hab hbarrier hint hscalar)




theorem actualCapTopEntry_action_gt
    {X : Type u} [TopologicalSpace X] {time : X → ℝ}
    {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    {T tau a b c ell theta offset h : ℝ} {x y : G.Point}
    (p : M14BackwardPath G T 0 tau x y)
    (hc : 0 < c) (hthetaOne : theta < 1)
    (hbudget : ell < -(c / 2) * (Real.log (1 - theta) + Real.log 2))
    (hh : 0 < h) (ha : 0 < a) (hab : a ≤ b) (hbtau : b ≤ tau)
    (htop : (offset - a) / h ^ 2 = theta)
    (hinner : (offset - b) / h ^ 2 ≤ 1 / 2)
    (hscalar : ∀ t ∈ Ioo a b,
      c / (2 * (1 - (offset - t) / h ^ 2) * h ^ 2) ≤
        horizontalScalarCurvature G.leafwise (p.curve t)) :
    ell < ∫ t in a..b, pathPositiveDensity p t := by
  apply capPhysicalTopAction_gt hc hthetaOne hbudget (sq_pos_of_pos hh) hab htop hinner
    (pathPositiveDensity p) (pathPositiveDensity_tail_integrable hM12 p ha hab hbtau)
  intro t ht
  apply (hscalar t ht).trans
  dsimp only [pathPositiveDensity]
  apply (le_max_left _ _).trans (le_add_of_nonneg_right ?_)
  by_cases hv : p.horizontal_velocity t = 0
  · simp only [hv, map_zero, le_refl]
  · exact (G.spacetime.horizontalMetric.pos (p.curve t) (p.horizontal_velocity t) hv).le

end PoincareConjecture.Proofs.M46
