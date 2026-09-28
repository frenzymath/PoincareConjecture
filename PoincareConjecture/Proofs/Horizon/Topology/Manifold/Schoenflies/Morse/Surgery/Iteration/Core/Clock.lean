import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.MeanValue



noncomputable section
set_option autoImplicit false

open Set
open scoped ContDiff

namespace Poincare.Manifold.Schoenflies



def capStretchClock (K t : Real) : Real :=
  t + K * Real.smoothTransition (4 * t - 1)

theorem contDiff_capStretchClock (K : Real) : ContDiff Real ∞ (capStretchClock K) :=
  contDiff_id.add (contDiff_const.mul (Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)))

theorem capStretchClock_eq_self (K : Real) {t : Real} (ht : t ≤ 1 / 4) :
    capStretchClock K t = t := by
  simp [capStretchClock, Real.smoothTransition.zero_of_nonpos (by linarith : 4 * t - 1 ≤ 0)]

theorem capStretchClock_eq_add (K : Real) {t : Real} (ht : 1 / 2 ≤ t) :
    capStretchClock K t = t + K := by
  simp [capStretchClock, Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 4 * t - 1)]

theorem deriv_capStretchClock_pos {K : Real} (hK : 0 ≤ K) (t : Real) :
    0 < deriv (capStretchClock K) t := by
  let w : Real → Real := fun u => Real.smoothTransition (4 * u - 1)
  have hw : ContDiff Real ∞ w := Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hwm : Monotone w := fun x y hxy => Real.smoothTransition.monotone (by linarith)
  have hd := (hasDerivAt_id t).add
    ((hw.differentiable (by simp) t).hasDerivAt.const_mul K)
  change HasDerivAt (capStretchClock K) (1 + K * deriv w t) t at hd
  rw [hd.deriv]
  linarith [mul_nonneg hK (hwm.deriv_nonneg (x := t))]


def capPhysicalClock (c s K h : Real) : Real :=
  c + s * capStretchClock K ((h - c) / s)

theorem contDiff_capPhysicalClock (c s K : Real) :
    ContDiff Real ∞ (capPhysicalClock c s K) :=
  contDiff_const.add (contDiff_const.mul ((contDiff_capStretchClock K).comp
    ((contDiff_id.sub contDiff_const).div_const s)))

theorem capPhysicalClock_at_normalized (c s K t : Real) (hs : s ≠ 0) :
    capPhysicalClock c s K (c + s * t) = c + s * capStretchClock K t := by
  simp only [capPhysicalClock, add_sub_cancel_left, mul_div_cancel_left₀ t hs]

theorem capPhysicalClock_eq_self (c s K : Real) (hs : s ≠ 0) {h : Real}
    (hh : (h - c) / s ≤ 1 / 4) : capPhysicalClock c s K h = h := by
  rw [capPhysicalClock, capStretchClock_eq_self K hh]
  field_simp
  ring

theorem deriv_capPhysicalClock_pos (c : Real) {s K : Real} (hs : s ≠ 0)
    (hK : 0 ≤ K) (h : Real) : 0 < deriv (capPhysicalClock c s K) h := by
  have hin : HasDerivAt (fun u : Real => (u - c) / s) (1 / s) h := by
    convert! ((hasDerivAt_id h).sub_const c).div_const s using 1
  have hcomp := ((contDiff_capStretchClock K).differentiable (by simp) _).hasDerivAt.comp h hin
  have hd := (hcomp.const_mul s).const_add c
  change HasDerivAt (capPhysicalClock c s K)
    (s * (deriv (capStretchClock K) ((h - c) / s) * (1 / s))) h at hd
  rw [hd.deriv]
  have heq : s * (deriv (capStretchClock K) ((h - c) / s) * (1 / s)) =
      deriv (capStretchClock K) ((h - c) / s) := by field_simp
  rw [heq]
  exact deriv_capStretchClock_pos hK _



theorem exists_cap_clock_avoiding_band (a b c : Real) {s : Real} (hs : s ≠ 0) :
    ∃ K : Real, 0 ≤ K ∧ ∀ t : Real, 1 / 2 ≤ t →
      capPhysicalClock c s K (c + s * t) ∉ Icc a b := by
  let K := (|a| + |b| + |c| + 1) / |s|
  have hK : 0 ≤ K := div_nonneg (by positivity) (abs_nonneg s)
  have hKs : |s| * K = |a| + |b| + |c| + 1 := by
    dsimp [K]
    field_simp
  refine ⟨K, hK, ?_⟩
  intro t ht
  rw [capPhysicalClock_at_normalized c s K t hs, capStretchClock_eq_add K ht]
  intro hband
  rcases lt_or_gt_of_ne hs with hsneg | hspos
  · rw [abs_of_neg hsneg] at hKs
    have hst : s * t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hsneg.le (by linarith)
    nlinarith [le_abs_self c, neg_abs_le a, hband.1, abs_nonneg b]
  · rw [abs_of_pos hspos] at hKs
    have hst : 0 ≤ s * t := mul_nonneg hspos.le (by linarith)
    nlinarith [neg_abs_le c, le_abs_self b, hband.2, abs_nonneg a]

end Poincare.Manifold.Schoenflies
