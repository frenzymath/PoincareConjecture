import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus











set_option autoImplicit false

open Set MeasureTheory
open scoped ContDiff Interval

namespace Real





theorem exists_smooth_clipped_identity {L delta : ℝ}
    (hL : 0 < L) (hdelta : 0 < delta) :
    ∃ a b : ℝ, ∃ chi : ℝ → ℝ,
      -L < a ∧ a < 0 ∧ 0 < b ∧ b < L ∧
      ContDiff ℝ ∞ chi ∧
      (∀ s, s ≤ a → chi s = chi (-L)) ∧
      (∀ s, b ≤ s → chi s = chi L) ∧
      (∀ s, |deriv chi s| ≤ 1) ∧
      (∀ s ∈ Icc (-L) L, |chi s - s| < delta) := by
  let eta := min (L / 8) (delta / 14)
  have heta : 0 < eta := lt_min (by positivity) (by positivity)
  have hetaL : eta ≤ L / 8 := min_le_left _ _
  have hetad : eta ≤ delta / 14 := min_le_right _ _
  let ell := L - 2 * eta
  have hell : eta < ell := by dsimp [ell]; linarith
  have hell0 : 0 < ell := heta.trans hell
  let H : ℝ → ℝ := fun t => smoothTransition (t / eta)
  have hHsmooth : ContDiff ℝ ∞ H :=
    smoothTransition.contDiff.comp (contDiff_id.div_const eta)
  have hHzero : ∀ t ≤ 0, H t = 0 := by
    intro t ht
    exact smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg ht heta.le)
  have hHone : ∀ t, eta ≤ t → H t = 1 := by
    intro t ht
    exact smoothTransition.one_of_one_le ((le_div_iff₀ heta).mpr (by simpa using ht))
  have hHnonneg : ∀ t, 0 ≤ H t := fun t => smoothTransition.nonneg (t / eta)
  have hHle : ∀ t, H t ≤ 1 := fun t => smoothTransition.le_one (t / eta)
  let F : ℝ → ℝ := fun t => ∫ u in 0..t, H u
  have hFder : ∀ t, HasDerivAt F (H t) t := fun t =>
    (hHsmooth.continuous.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hFsmooth : ContDiff ℝ ∞ F := by
    apply contDiff_infty_iff_deriv.mpr
    refine ⟨fun t => (hFder t).differentiableAt, ?_⟩
    have hderiv : deriv F = H := funext (fun t => (hFder t).deriv)
    rw [hderiv]
    exact hHsmooth
  have hFzero : ∀ t ≤ 0, F t = 0 := by
    intro t ht
    change (∫ u in 0..t, H u) = 0
    calc
      (∫ u in 0..t, H u) = ∫ _u in 0..t, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_ge ht]
        exact fun u hu => hHzero u hu.2
      _ = 0 := by simp
  have hFbounds : ∀ t, 0 ≤ t → 0 ≤ F t ∧ F t ≤ t := by
    intro t ht
    constructor
    · exact intervalIntegral.integral_nonneg_of_forall ht hHnonneg
    · have hle := intervalIntegral.integral_mono_on (μ := volume) ht
        (hHsmooth.continuous.intervalIntegrable 0 t)
        (continuous_const.intervalIntegrable 0 t) (fun u _hu => hHle u)
      simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] using hle
  have hFlinear : ∀ t, eta ≤ t → F t = F eta + t - eta := by
    intro t ht
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hHsmooth.continuous.intervalIntegrable 0 eta)
      (hHsmooth.continuous.intervalIntegrable eta t)
    have hone : (∫ u in eta..t, H u) = t - eta := by
      calc
        (∫ u in eta..t, H u) = ∫ _u in eta..t, (1 : ℝ) := by
          apply intervalIntegral.integral_congr
          rw [uIcc_of_le ht]
          exact fun u hu => hHone u hu.1
        _ = t - eta := by simp
    change (∫ u in 0..t, H u) = (∫ u in 0..eta, H u) + t - eta
    rw [← hsplit, hone]
    ring
  have hFerror : ∀ t, |F t - max 0 t| ≤ eta := by
    intro t
    rcases le_or_gt t 0 with ht | ht
    · rw [hFzero t ht, max_eq_left ht, sub_self, abs_zero]
      exact heta.le
    · rw [max_eq_right ht.le, abs_le]
      by_cases hte : t ≤ eta
      · obtain ⟨hnonneg, hle⟩ := hFbounds t ht.le
        constructor <;> linarith
      · rw [hFlinear t (le_of_not_ge hte)]
        obtain ⟨hnonneg, hle⟩ := hFbounds eta heta.le
        constructor <;> linarith
  let chi : ℝ → ℝ := fun s => -ell + F (s + ell) - F (s - ell)
  have hchis : ContDiff ℝ ∞ chi :=
    (contDiff_const.add (hFsmooth.comp (contDiff_id.add contDiff_const))).sub
      (hFsmooth.comp (contDiff_id.sub contDiff_const))
  have hchider : ∀ s, deriv chi s = H (s + ell) - H (s - ell) := by
    intro s
    have hp := (((hFder (s + ell)).comp s
      ((hasDerivAt_id s).add_const ell)).const_add (-ell)).fun_sub
      ((hFder (s - ell)).comp s ((hasDerivAt_id s).sub_const ell))
    simpa only [chi, Function.comp_def, id_eq, mul_one] using hp.deriv
  have hchileft : ∀ s ≤ -ell, chi s = -ell := by
    intro s hs
    dsimp [chi]
    rw [hFzero (s + ell) (by linarith), hFzero (s - ell) (by linarith)]
    ring
  have hchiright : ∀ s, ell + eta ≤ s → chi s = ell := by
    intro s hs
    dsimp [chi]
    rw [hFlinear (s + ell) (by linarith), hFlinear (s - ell) (by linarith)]
    ring
  refine ⟨-ell, ell + eta, chi, ?_, ?_, ?_, ?_, hchis, ?_, ?_, ?_, ?_⟩
  · dsimp [ell]
    linarith
  · linarith
  · positivity
  · dsimp [ell]
    linarith
  · intro s hs
    rw [hchileft s hs, hchileft (-L) (by dsimp [ell]; linarith)]
  · intro s hs
    rw [hchiright s hs, hchiright L (by dsimp [ell]; linarith)]
  · intro s
    rw [hchider, abs_le]
    have hleft0 := hHnonneg (s + ell)
    have hleft1 := hHle (s + ell)
    have hright0 := hHnonneg (s - ell)
    have hright1 := hHle (s - ell)
    constructor <;> linarith
  · intro s hs
    let Q : ℝ := -ell + max 0 (s + ell) - max 0 (s - ell)
    have happrox : |chi s - Q| ≤ 2 * eta := by
      have h1 := abs_le.mp (hFerror (s + ell))
      have h2 := abs_le.mp (hFerror (s - ell))
      dsimp [chi, Q]
      rw [abs_le]
      constructor <;> linarith
    have hclamp : |Q - s| ≤ 2 * eta := by
      dsimp [Q]
      rw [abs_le]
      have hlow := hs.1
      have hhigh := hs.2
      dsimp [ell]
      constructor <;> simp only [max_def] <;> split_ifs <;> linarith
    calc
      |chi s - s| ≤ |chi s - Q| + |Q - s| := abs_sub_le _ _ _
      _ ≤ 2 * eta + 2 * eta := add_le_add happrox hclamp
      _ < delta := by linarith

end Real
