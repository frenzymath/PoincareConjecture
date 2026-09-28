
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

















namespace Poincare

theorem pinchingAuxiliaryEqCompletedSquare (lam X Y : ℝ) :
    X * Y ^ 2 + lam * Y * (Y - X) + lam ^ 2 * (X - Y) =
      Y ^ 3 + (X - Y) * ((lam - Y / 2) ^ 2 + 3 * Y ^ 2 / 4) := by
  ring

theorem pinchingAuxiliaryNonneg {lam X Y : ℝ}
    (hX : 0 ≤ X) (hYX : Y ≤ X) (hlam : -Y ≤ lam) :
    0 ≤ X * Y ^ 2 + lam * Y * (Y - X) + lam ^ 2 * (X - Y) := by
  have hXY : 0 ≤ X - Y := sub_nonneg.mpr hYX
  by_cases hY : Y ≤ 0
  · have hlam0 : 0 ≤ lam := (neg_nonneg.mpr hY).trans hlam
    have hnegY : 0 ≤ -Y := neg_nonneg.mpr hY
    calc
      0 ≤ X * Y ^ 2 + lam * (-Y) * (X - Y) + lam ^ 2 * (X - Y) := by
        positivity
      _ = X * Y ^ 2 + lam * Y * (Y - X) + lam ^ 2 * (X - Y) := by ring
  · rw [pinchingAuxiliaryEqCompletedSquare]
    have hY0 : 0 < Y := lt_of_not_ge hY
    positivity

theorem pinchingAuxiliaryNonnegOfOrderedEigenvalues {lam mu nu : ℝ}
    (hmu : mu ≤ lam) (hnu : nu ≤ mu) (hnu0 : nu ≤ 0) :
    0 ≤ (-nu) * (-mu) ^ 2 + lam * (-mu) * ((-mu) - (-nu)) +
      lam ^ 2 * ((-nu) - (-mu)) := by
  apply pinchingAuxiliaryNonneg
  · exact neg_nonneg.mpr hnu0
  · exact neg_le_neg hnu
  · simpa only [neg_neg] using hmu

theorem pinchingInitialTraceLowerBound {lam mu nu : ℝ}
    (hmu : mu ≤ lam) (hnu : nu ≤ mu) (hnuLower : -1 ≤ nu) :
    -3 ≤ lam + mu + nu := by
  linarith

theorem pinchingInitialTraceLowerBoundOfMaxNegLeOne
    {lam mu nu : ℝ} (hmu : mu ≤ lam) (hnu : nu ≤ mu)
    {X : ℝ} (hX : X = max (-nu) 0) (hXpos : 0 < X) (hXle : X ≤ 1) :
    X * (Real.log X - 3) ≤ lam + mu + nu := by
  have hneg : 0 < -nu := by
    by_contra h
    have hnonpos : -nu ≤ 0 := le_of_not_gt h
    rw [max_eq_right hnonpos] at hX
    linarith
  have hnuNonpos : -nu ≥ 0 := le_of_lt hneg
  have hXeq : X = -nu := by
    rw [hX, max_eq_left hnuNonpos]
  have hlog : Real.log X ≤ 0 := Real.log_nonpos hXpos.le hXle
  have htrace : -3 * X ≤ lam + mu + nu := by
    rw [hXeq]
    linarith
  have hbarrier : X * (Real.log X - 3) ≤ -3 * X := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (le_of_lt hXpos) hlog]
  exact hbarrier.trans htrace

theorem pinchingReactionIdentity (lam X Y : ℝ) :
    X * (X ^ 2 + Y ^ 2 + lam ^ 2 + X * Y - lam * (X + Y)) -
        ((lam - X - Y) + X) * (-X ^ 2 + Y * lam) =
      X ^ 3 + (X * Y ^ 2 + lam * Y * (Y - X) + lam ^ 2 * (X - Y)) := by
  ring

theorem pinchingReactionInequality {lam X Y : ℝ}
    (hX : 0 ≤ X) (hYX : Y ≤ X) (hlam : -Y ≤ lam) :
    X ^ 3 ≤
      X * (X ^ 2 + Y ^ 2 + lam ^ 2 + X * Y - lam * (X + Y)) -
        ((lam - X - Y) + X) * (-X ^ 2 + Y * lam) := by
  rw [pinchingReactionIdentity]
  exact le_add_of_nonneg_right (pinchingAuxiliaryNonneg hX hYX hlam)

theorem derivPinchingLogQuantityGe {S X : ℝ → ℝ} {t dS dX : ℝ}
    (hS : HasDerivAt S dS t) (hX : HasDerivAt X dX t)
    (hXpos : 0 < X t)
    (hineq : X t ^ 3 ≤ X t * dS - (S t + X t) * dX) :
    X t ≤ deriv (fun s => S s / X s - Real.log (X s)) t := by
  have hXne : X t ≠ 0 := ne_of_gt hXpos
  have hderiv := (hS.div hX hXne).sub (hX.log hXne)
  change HasDerivAt (fun s => S s / X s - Real.log (X s))
    ((dS * X t - S t * dX) / X t ^ 2 - dX / X t) t at hderiv
  rw [hderiv.deriv]
  have hid : (dS * X t - S t * dX) / X t ^ 2 - dX / X t =
      (X t * dS - (S t + X t) * dX) / X t ^ 2 := by
    field_simp
    ring
  rw [hid]
  apply (le_div_iff₀ (sq_pos_of_pos hXpos)).mpr
  convert hineq using 1 <;> first | rfl | ring

end Poincare
