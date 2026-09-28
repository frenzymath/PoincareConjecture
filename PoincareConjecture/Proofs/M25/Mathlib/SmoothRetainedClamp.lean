import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus











set_option autoImplicit false

open Set MeasureTheory
open scoped ContDiff Interval

namespace Real





theorem exists_smooth_retained_clamp {a₀ a b b₀ : ℝ}
    (hleft : a₀ < a) (hab : a < b) (hright : b < b₀) :
    ∃ rho : ℝ → ℝ,
      ContDiff ℝ ∞ rho ∧ Monotone rho ∧
      (∀ s : ℝ, rho s ∈ Ioo a₀ b₀) ∧
      EqOn rho id (Icc a b) ∧
      (∀ s : ℝ, deriv rho s ∈ Icc 0 1) ∧
      (∀ s : ℝ, s ≤ a₀ → rho s = rho a₀) ∧
      (∀ s : ℝ, b₀ ≤ s → rho s = rho b₀) := by
  let ell : ℝ := (a₀ + a) / 2
  let u : ℝ := (b + b₀) / 2
  have ha₀ell : a₀ < ell := by dsimp [ell]; linarith
  have hella : ell < a := by dsimp [ell]; linarith
  have hbu : b < u := by dsimp [u]; linarith
  have hub₀ : u < b₀ := by dsimp [u]; linarith
  have hdenleft : 0 < a - ell := sub_pos.mpr hella
  have hdenright : 0 < u - b := sub_pos.mpr hbu
  let w : ℝ → ℝ := fun s =>
    smoothTransition ((s - ell) / (a - ell)) *
      smoothTransition ((u - s) / (u - b))
  have hwsmooth : ContDiff ℝ ∞ w :=
    (smoothTransition.contDiff.comp
      ((contDiff_id.sub contDiff_const).div_const (a - ell))).mul
      (smoothTransition.contDiff.comp
        ((contDiff_const.sub contDiff_id).div_const (u - b)))
  have hwbounds (s : ℝ) : w s ∈ Icc 0 1 := by
    have hl0 := smoothTransition.nonneg ((s - ell) / (a - ell))
    have hl1 := smoothTransition.le_one ((s - ell) / (a - ell))
    have hr0 := smoothTransition.nonneg ((u - s) / (u - b))
    have hr1 := smoothTransition.le_one ((u - s) / (u - b))
    change 0 ≤ smoothTransition ((s - ell) / (a - ell)) *
        smoothTransition ((u - s) / (u - b)) ∧
      smoothTransition ((s - ell) / (a - ell)) *
        smoothTransition ((u - s) / (u - b)) ≤ 1
    constructor
    · exact mul_nonneg hl0 hr0
    · nlinarith [mul_nonneg (sub_nonneg.mpr hl1) hr0]
  have hwleft (s : ℝ) (hs : s ≤ ell) : w s = 0 := by
    change smoothTransition ((s - ell) / (a - ell)) *
      smoothTransition ((u - s) / (u - b)) = 0
    rw [smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs) hdenleft.le), zero_mul]
  have hwright (s : ℝ) (hs : u ≤ s) : w s = 0 := by
    change smoothTransition ((s - ell) / (a - ell)) *
      smoothTransition ((u - s) / (u - b)) = 0
    rw [smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs) hdenright.le), mul_zero]
  have hwone (s : ℝ) (hs : s ∈ Icc a b) : w s = 1 := by
    have hl : smoothTransition ((s - ell) / (a - ell)) = 1 :=
      smoothTransition.one_of_one_le
        ((le_div_iff₀ hdenleft).mpr (by linarith [hs.1]))
    have hr : smoothTransition ((u - s) / (u - b)) = 1 :=
      smoothTransition.one_of_one_le
        ((le_div_iff₀ hdenright).mpr (by linarith [hs.2]))
    simp only [w, hl, hr, mul_one]
  let rho : ℝ → ℝ := fun s => a + ∫ t in a..s, w t
  have hrder (s : ℝ) : HasDerivAt rho (w s) s :=
    (hwsmooth.continuous.integral_hasStrictDerivAt a s).hasDerivAt.const_add a
  have hderiv : deriv rho = w := funext (fun s => (hrder s).deriv)
  have hrsmooth : ContDiff ℝ ∞ rho := by
    apply contDiff_infty_iff_deriv.mpr
    refine ⟨fun s => (hrder s).differentiableAt, ?_⟩
    rw [hderiv]
    exact hwsmooth
  have hrmono : Monotone rho :=
    monotone_of_deriv_nonneg (fun s => (hrder s).differentiableAt)
      (fun s => by rw [hderiv]; exact (hwbounds s).1)
  have hrleft (s : ℝ) (hs : s ≤ ell) : rho s = rho ell := by
    have hzero : (∫ t in s..ell, w t) = 0 := by
      calc
        (∫ t in s..ell, w t) = ∫ _t in s..ell, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          rw [uIcc_of_le hs]
          exact fun t ht => hwleft t ht.2
        _ = 0 := by simp
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hwsmooth.continuous.intervalIntegrable a s)
      (hwsmooth.continuous.intervalIntegrable s ell)
    dsimp only [rho]
    rw [← hsplit, hzero, add_zero]
  have hrright (s : ℝ) (hs : u ≤ s) : rho s = rho u := by
    have hzero : (∫ t in u..s, w t) = 0 := by
      calc
        (∫ t in u..s, w t) = ∫ _t in u..s, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          rw [uIcc_of_le hs]
          exact fun t ht => hwright t ht.1
        _ = 0 := by simp
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hwsmooth.continuous.intervalIntegrable a u)
      (hwsmooth.continuous.intervalIntegrable u s)
    dsimp only [rho]
    rw [← hsplit, hzero, add_zero]
  have hrlower : ell ≤ rho ell := by
    have hcomp := intervalIntegral.integral_mono_on (μ := volume) hella.le
      (hwsmooth.continuous.intervalIntegrable ell a)
      (continuous_const.intervalIntegrable ell a) (fun t _ => (hwbounds t).2)
    have hint : (∫ t in ell..a, w t) ≤ a - ell := by simpa using hcomp
    dsimp only [rho]
    rw [intervalIntegral.integral_symm ell a]
    linarith
  have hrupper : rho u ≤ u := by
    have hau : a ≤ u := (hab.trans hbu).le
    have hcomp := intervalIntegral.integral_mono_on (μ := volume) hau
      (hwsmooth.continuous.intervalIntegrable a u)
      (continuous_const.intervalIntegrable a u) (fun t _ => (hwbounds t).2)
    have hint : (∫ t in a..u, w t) ≤ u - a := by simpa using hcomp
    dsimp only [rho]
    linarith
  have hrrange (s : ℝ) : rho s ∈ Ioo a₀ b₀ := by
    have hlo : rho ell ≤ rho s := by
      rcases le_total s ell with hs | hs
      · exact (hrleft s hs).ge
      · exact hrmono hs
    have hhi : rho s ≤ rho u := by
      rcases le_total s u with hs | hs
      · exact hrmono hs
      · exact (hrright s hs).le
    exact ⟨ha₀ell.trans_le (hrlower.trans hlo), (hhi.trans hrupper).trans_lt hub₀⟩
  have hragree : EqOn rho id (Icc a b) := by
    intro s hs
    have hint : (∫ t in a..s, w t) = s - a := by
      calc
        (∫ t in a..s, w t) = ∫ _t in a..s, (1 : ℝ) := by
          apply intervalIntegral.integral_congr
          rw [uIcc_of_le hs.1]
          exact fun t ht => hwone t ⟨ht.1, ht.2.trans hs.2⟩
        _ = s - a := by simp
    change a + (∫ t in a..s, w t) = s
    rw [hint]
    ring
  refine ⟨rho, hrsmooth, hrmono, hrrange, hragree, ?_, ?_, ?_⟩
  · intro s
    rw [hderiv]
    exact hwbounds s
  · intro s hs
    rw [hrleft s (hs.trans ha₀ell.le), hrleft a₀ ha₀ell.le]
  · intro s hs
    rw [hrright s (hub₀.le.trans hs), hrright b₀ hub₀.le]

end Real
