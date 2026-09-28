import PoincareConjecture.Proofs.M09.EnergyBound
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic











set_option autoImplicit false

open Set
open scoped Topology intervalIntegral

namespace PoincareConjecture.M14




theorem nonnegativeEnergy_pair_bound_within (e e' : ℝ → ℝ) {H A : ℝ}
    (hA : 0 ≤ A) (hc : ContinuousOn e (Icc 0 H))
    (he : ∀ s ∈ Icc 0 H, 0 ≤ e s)
    (hd : ∀ s ∈ Icc 0 H, HasDerivWithinAt e (e' s) (Icc 0 H) s)
    (hbound : ∀ s ∈ Icc 0 H, |e' s| ≤ A * (e s + 1))
    {r t : ℝ} (hr : r ∈ Icc 0 H) (ht : t ∈ Icc 0 H) :
    e r + 1 ≤ (e t + 1) * Real.exp (A * H) := by
  let c : ℝ → ℝ := fun s => t + s * (r - t)
  have hmap : MapsTo c (Icc 0 1) (Icc 0 H) := by
    intro s hs
    dsimp [c]
    constructor
    · nlinarith [mul_nonneg hs.1 hr.1, mul_nonneg (sub_nonneg.mpr hs.2) ht.1]
    · nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr hr.2),
        mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr ht.2)]
  have hcn : ∀ s ∈ Icc 0 1, 0 ≤ e (c s) + 1 :=
    fun s hs => by linarith [he (c s) (hmap hs)]
  have hrt : |r - t| ≤ H := abs_le.mpr ⟨by linarith [hr.1, ht.2],
    by linarith [hr.2, ht.1]⟩
  have hcd (s : ℝ) : HasDerivAt c (r - t) s := by
    simpa only [c, id_eq, one_mul] using ((hasDerivAt_id s).mul_const (r - t)).const_add t
  have hf : ContinuousOn (fun s => e (c s) + 1) (Icc 0 1) :=
    (hc.comp (continuous_const.add
      (continuous_id.mul continuous_const)).continuousOn hmap).add_const 1
  have hdf : ∀ s ∈ Ico 0 1,
      HasDerivWithinAt (fun s => e (c s) + 1) (e' (c s) * (r - t)) (Ici s) s := by
    intro s hs
    have h := ((hd (c s) (hmap ⟨hs.1, hs.2.le⟩)).comp s
      (hcd s).hasDerivWithinAt hmap).add_const 1
    exact h.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hs)
  have hbf : ∀ s ∈ Ico 0 1,
      ‖e' (c s) * (r - t)‖ ≤ A * H * ‖e (c s) + 1‖ + 0 := by
    intro s hs
    have hn := hcn s ⟨hs.1, hs.2.le⟩
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs, abs_of_nonneg hn, add_zero]
    calc
      _ ≤ (A * (e (c s) + 1)) * H :=
        mul_le_mul (hbound (c s) (hmap ⟨hs.1, hs.2.le⟩)) hrt
          (abs_nonneg _) (mul_nonneg hA hn)
      _ = _ := by ring
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le hf hdf
    (δ := e t + 1) (K := A * H) (ε := 0)
    (by simpa only [c, zero_mul, add_zero, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ e t + 1 by linarith [he t ht])]
        using le_refl (e t + 1)) hbf 1
    (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
  have hc1 : c 1 = r := by dsimp [c]; ring
  simpa only [hc1, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ e r + 1 by linarith [he r hr]), gronwallBound_ε0,
    sub_zero, mul_one] using hg



theorem nonnegativeEnergy_integral_bound_within (e e' : ℝ → ℝ) {H A : ℝ}
    (hH : 0 ≤ H) (hA : 0 ≤ A) (hc : ContinuousOn e (Icc 0 H))
    (he : ∀ s ∈ Icc 0 H, 0 ≤ e s)
    (hd : ∀ s ∈ Icc 0 H, HasDerivWithinAt e (e' s) (Icc 0 H) s)
    (hbound : ∀ s ∈ Icc 0 H, |e' s| ≤ A * (e s + 1))
    {r : ℝ} (hr : r ∈ Icc 0 H) :
    H * (e r + 1) ≤ Real.exp (A * H) * (∫ s in (0 : ℝ)..H, e s + 1) := by
  have hi : IntervalIntegrable (fun s => e s + 1) MeasureTheory.volume 0 H := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hH] using hc.add_const 1
  have hm := intervalIntegral.integral_mono_on hH intervalIntegrable_const
    (hi.const_mul (Real.exp (A * H))) (fun t ht => by
      simpa only [mul_comm] using
        nonnegativeEnergy_pair_bound_within e e' hA hc he hd hbound hr ht)
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul,
    intervalIntegral.integral_const_mul] using hm




theorem nonnegativeEnergy_action_bound_within (e e' R : ℝ → ℝ) {H A C : ℝ}
    (hH : 0 ≤ H) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hc : ContinuousOn e (Icc 0 H)) (he : ∀ s ∈ Icc 0 H, 0 ≤ e s)
    (hd : ∀ s ∈ Icc 0 H, HasDerivWithinAt e (e' s) (Icc 0 H) s)
    (hbound : ∀ s ∈ Icc 0 H, |e' s| ≤ A * (e s + 1))
    (hRc : ContinuousOn R (Icc 0 H)) (hR : ∀ s ∈ Icc 0 H, -C ≤ R s)
    {r : ℝ} (hr : r ∈ Icc 0 H) :
    H * (e r + 1) ≤ Real.exp (A * H) *
      (2 * (∫ s in (0 : ℝ)..H, 2 * s ^ 2 * R s + (1 / 2 : ℝ) * e s) +
        4 * C * H ^ 3 + H) := by
  let L : ℝ → ℝ := fun s => 2 * s ^ 2 * R s + (1 / 2 : ℝ) * e s
  have hi : IntervalIntegrable e MeasureTheory.volume 0 H := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hH] using hc
  have hLi : IntervalIntegrable L MeasureTheory.volume 0 H := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hH]
    exact ((continuousOn_const.mul (continuousOn_id.pow 2)).mul hRc).add
      (continuousOn_const.mul hc)
  have hpoint : ∀ s ∈ Icc 0 H, e s ≤ 2 * L s + 4 * C * H ^ 2 := by
    intro s hs
    have hs2 : s ^ 2 ≤ H ^ 2 := by nlinarith [hs.1, hs.2]
    have h1 := mul_le_mul_of_nonneg_left (hR s hs) (sq_nonneg s)
    have h2 := mul_le_mul_of_nonneg_left hs2 hC
    dsimp [L]
    nlinarith
  have henergy := intervalIntegral.integral_mono_on hH hi
    ((hLi.const_mul 2).add intervalIntegrable_const) hpoint
  rw [intervalIntegral.integral_add (hLi.const_mul 2) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at henergy
  simp only [sub_zero, smul_eq_mul] at henergy
  have hreverse := nonnegativeEnergy_integral_bound_within e e' hH hA hc he hd hbound hr
  rw [intervalIntegral.integral_add hi intervalIntegrable_const,
    intervalIntegral.integral_const] at hreverse
  simp only [sub_zero, smul_eq_mul, mul_one] at hreverse
  apply hreverse.trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  dsimp [L] at henergy
  nlinarith

end PoincareConjecture.M14
