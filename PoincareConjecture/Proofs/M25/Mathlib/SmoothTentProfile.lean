import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus











set_option autoImplicit false

open Set MeasureTheory
open scoped ContDiff Interval

namespace Real





theorem exists_smooth_tent_profile {L delta : ℝ} (hL : 0 < L) (hdelta : 0 < delta) :
    ∃ a b : ℝ, ∃ phi : ℝ → ℝ,
      -L < a ∧ b < L ∧ ContDiff ℝ ∞ phi ∧
      Function.support phi ⊆ Icc a b ∧
      (∀ s, |deriv phi s| ≤ 1) ∧
      (∀ s, |phi s - max 0 (L - |s|)| < delta) := by
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
  let phi : ℝ → ℝ := fun s => F (s + ell) - 2 * F s + F (s - ell)
  have hphis : ContDiff ℝ ∞ phi :=
    ((hFsmooth.comp (contDiff_id.add contDiff_const)).sub
      (contDiff_const.mul hFsmooth)).add
      (hFsmooth.comp (contDiff_id.sub contDiff_const))
  have hphider : ∀ s, deriv phi s = H (s + ell) - 2 * H s + H (s - ell) := by
    intro s
    have hp := (((hFder (s + ell)).comp s ((hasDerivAt_id s).add_const ell)).fun_sub
      ((hFder s).const_mul 2)).fun_add
      ((hFder (s - ell)).comp s ((hasDerivAt_id s).sub_const ell))
    simpa only [phi, Function.comp_def, id_eq, mul_one]
      using hp.deriv
  refine ⟨-ell, ell + eta, phi, ?_, ?_, hphis, ?_, ?_, ?_⟩
  · dsimp [ell]
    linarith
  · dsimp [ell]
    linarith
  · intro s hs
    by_contra hnot
    have hnonzero : phi s ≠ 0 := hs
    apply hnonzero
    rcases not_and_or.mp hnot with hleft | hright
    · have hlt : s < -ell := lt_of_not_ge hleft
      dsimp [phi]
      rw [hFzero (s + ell) (by linarith), hFzero s (by linarith),
        hFzero (s - ell) (by linarith)]
      ring
    · have hlt : ell + eta < s := lt_of_not_ge hright
      dsimp [phi]
      rw [hFlinear (s + ell) (by linarith), hFlinear s (by linarith),
        hFlinear (s - ell) (by linarith)]
      ring
  · intro s
    rw [hphider]
    rcases le_or_gt s 0 with hs | hs
    · rw [hHzero s hs, hHzero (s - ell) (by linarith)]
      simpa only [mul_zero, sub_zero, add_zero, abs_of_nonneg (hHnonneg _)] using hHle (s + ell)
    · by_cases hse : s ≤ eta
      · rw [hHone (s + ell) (by linarith), hHzero (s - ell) (by linarith), add_zero,
          abs_le]
        have h0 := hHnonneg s
        have h1 := hHle s
        constructor <;> linarith
      · rw [hHone (s + ell) (by linarith), hHone s (le_of_not_ge hse), abs_le]
        have h0 := hHnonneg (s - ell)
        have h1 := hHle (s - ell)
        constructor <;> linarith
  · intro s
    have htent : max 0 (s + ell) - 2 * max 0 s + max 0 (s - ell) =
        max 0 (ell - |s|) := by
      rcases le_or_gt 0 s with hs | hs
      · rw [abs_of_nonneg hs, max_eq_right (by linarith : 0 ≤ s + ell), max_eq_right hs]
        by_cases hse : s ≤ ell
        · rw [max_eq_left (by linarith : s - ell ≤ 0),
            max_eq_right (by linarith : 0 ≤ ell - s)]
          ring
        · rw [max_eq_right (by linarith : 0 ≤ s - ell),
            max_eq_left (by linarith : ell - s ≤ 0)]
          ring
      · rw [abs_of_neg hs, max_eq_left hs.le,
          max_eq_left (by linarith : s - ell ≤ 0)]
        simp only [mul_zero, sub_zero, add_zero, sub_neg_eq_add]
        rw [add_comm ell s]
    have happrox : |phi s - max 0 (ell - |s|)| ≤ 4 * eta := by
      rw [← htent]
      have h1 := abs_le.mp (hFerror (s + ell))
      have h2 := abs_le.mp (hFerror s)
      have h3 := abs_le.mp (hFerror (s - ell))
      dsimp [phi]
      rw [abs_le]
      constructor <;> linarith
    have hheight : |max 0 (ell - |s|) - max 0 (L - |s|)| ≤ 2 * eta := by
      rw [abs_le]
      dsimp [ell]
      constructor <;> simp only [max_def] <;> split_ifs <;> linarith
    calc
      |phi s - max 0 (L - |s|)| ≤
          |phi s - max 0 (ell - |s|)| +
            |max 0 (ell - |s|) - max 0 (L - |s|)| := abs_sub_le _ _ _
      _ ≤ 4 * eta + 2 * eta := add_le_add happrox hheight
      _ < delta := by linarith

end Real
