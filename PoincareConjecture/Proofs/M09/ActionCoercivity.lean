import PoincareConjecture.Proofs.M09.EnergyBound
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped intervalIntegral

namespace PoincareConjecture.Proofs.M09

theorem nonnegativeEnergy_reverse_exp_bound (e e' : ℝ → ℝ) (H A : ℝ)
    (_hH : 0 ≤ H) (hA : 0 ≤ A)
    (hc : ContinuousOn e (Set.Icc 0 H))
    (he : ∀ s ∈ Set.Icc 0 H, 0 ≤ e s)
    (hd : ∀ s ∈ Set.Icc 0 H, HasDerivAt e (e' s) s)
    (hbound : ∀ s ∈ Set.Icc 0 H, |e' s| ≤ A * (e s + 1)) :
    ∀ s ∈ Set.Icc 0 H, e 0 + 1 ≤ (e s + 1) * Real.exp (A * s) := by
  intro s hs
  let er : ℝ → ℝ := fun r ↦ e (s - r)
  let er' : ℝ → ℝ := fun r ↦ -e' (s - r)
  have hmap : Set.MapsTo (fun r : ℝ ↦ s - r) (Set.Icc 0 s) (Set.Icc 0 H) := by
    intro r hr
    change 0 ≤ s - r ∧ s - r ≤ H
    constructor <;> linarith [hr.1, hr.2, hs.2]
  have hce : ContinuousOn er (Set.Icc 0 s) := by
    exact hc.comp (continuousOn_const.sub continuousOn_id) hmap
  have hee : ∀ r ∈ Set.Icc 0 s, 0 ≤ er r := fun r hr ↦ he (s - r) (hmap hr)
  have hde : ∀ r ∈ Set.Ico 0 s, HasDerivAt er (er' r) r := by
    intro r hr
    have h := (hd (s - r) (hmap ⟨hr.1, hr.2.le⟩)).comp r
      ((hasDerivAt_const r s).sub (hasDerivAt_id r))
    simpa only [Function.comp_def, er, er', zero_sub, mul_neg_one] using h
  have hbe : ∀ r ∈ Set.Ico 0 s, |er' r| ≤ A * (er r + 1) := by
    intro r hr
    simpa only [er', er, abs_neg] using hbound (s - r) (hmap ⟨hr.1, hr.2.le⟩)
  have h := nonnegativeEnergy_exp_bound er er' s A hs.1 hA hce hee hde hbe s
    ⟨hs.1, le_rfl⟩
  simpa only [er, sub_self, sub_zero, mul_comm] using h

theorem nonnegativeEnergy_integral_reverse_bound (e e' : ℝ → ℝ) (H A : ℝ)
    (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hc : ContinuousOn e (Set.Icc 0 H))
    (he : ∀ s ∈ Set.Icc 0 H, 0 ≤ e s)
    (hd : ∀ s ∈ Set.Icc 0 H, HasDerivAt e (e' s) s)
    (hbound : ∀ s ∈ Set.Icc 0 H, |e' s| ≤ A * (e s + 1)) :
    H * (e 0 + 1) ≤ Real.exp (A * H) *
      (∫ s in (0 : ℝ)..H, e s + 1) := by
  have hpoint : ∀ s ∈ Set.Icc 0 H, e 0 + 1 ≤
      Real.exp (A * H) * (e s + 1) := by
    intro s hs
    calc
      e 0 + 1 ≤ (e s + 1) * Real.exp (A * s) :=
        nonnegativeEnergy_reverse_exp_bound e e' H A hH hA hc he hd hbound s hs
      _ ≤ (e s + 1) * Real.exp (A * H) := by
        have hexp : Real.exp (A * s) ≤ Real.exp (A * H) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 hA)
        exact mul_le_mul_of_nonneg_left hexp (by linarith [he s hs])
      _ = Real.exp (A * H) * (e s + 1) := by ring
  have hi : IntervalIntegrable (fun s : ℝ ↦ e s + 1) MeasureTheory.volume 0 H := by
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le hH] using hc.add_const 1
  have hconst : IntervalIntegrable (fun _ : ℝ ↦ e 0 + 1) MeasureTheory.volume 0 H :=
    continuousOn_const.intervalIntegrable
  have hm := intervalIntegral.integral_mono_on hH hconst (hi.const_mul (Real.exp (A * H)))
    (fun s hs ↦ hpoint s hs)
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_smul,
    intervalIntegral.integral_const_mul] using hm

theorem nonnegativeEnergy_action_reverse_bound (e e' R : ℝ → ℝ) (H A C : ℝ)
    (hH : 0 ≤ H) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hc : ContinuousOn e (Set.Icc 0 H))
    (he : ∀ s ∈ Set.Icc 0 H, 0 ≤ e s)
    (hd : ∀ s ∈ Set.Icc 0 H, HasDerivAt e (e' s) s)
    (hbound : ∀ s ∈ Set.Icc 0 H, |e' s| ≤ A * (e s + 1))
    (hRc : ContinuousOn R (Set.Icc 0 H))
    (hR : ∀ s ∈ Set.Icc 0 H, |R s| ≤ C) :
    H * (e 0 + 1) ≤ Real.exp (A * H) *
      (2 * (∫ s in (0 : ℝ)..H, 2 * s ^ 2 * R s + (1 / 2 : ℝ) * e s) +
        4 * C * H ^ 3 + H) := by
  let L : ℝ → ℝ := fun s ↦ 2 * s ^ 2 * R s + (1 / 2 : ℝ) * e s
  have hi : IntervalIntegrable e MeasureTheory.volume 0 H := by
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le hH] using hc
  have hLi : IntervalIntegrable L MeasureTheory.volume 0 H := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hH]
    exact ((continuousOn_const.mul (continuousOn_id.pow 2)).mul hRc).add
      (continuousOn_const.mul hc)
  have hpoint : ∀ s ∈ Set.Icc 0 H, e s ≤ 2 * L s + 4 * C * H ^ 2 := by
    intro s hs
    have hRlo := (abs_le.mp (hR s hs)).1
    have hs2 : s ^ 2 ≤ H ^ 2 := by nlinarith [hs.1, hs.2]
    have h1 := mul_le_mul_of_nonneg_left hRlo (sq_nonneg s)
    have h2 := mul_le_mul_of_nonneg_left hs2 hC
    dsimp [L]
    nlinarith
  have henergy := intervalIntegral.integral_mono_on hH hi
    ((hLi.const_mul 2).add intervalIntegrable_const) hpoint
  rw [intervalIntegral.integral_add (hLi.const_mul 2) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at henergy
  simp only [sub_zero, smul_eq_mul] at henergy
  have hreverse := nonnegativeEnergy_integral_reverse_bound e e' H A hH hA hc he hd hbound
  rw [intervalIntegral.integral_add hi intervalIntegrable_const,
    intervalIntegral.integral_const] at hreverse
  simp only [sub_zero, smul_eq_mul, mul_one] at hreverse
  apply hreverse.trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  dsimp [L] at henergy
  nlinarith

end PoincareConjecture.Proofs.M09
