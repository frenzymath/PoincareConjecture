import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic








set_option autoImplicit false

namespace PoincareConjecture.Proofs.M09

theorem regularizedEnergy_abs_bound (s H B C e dR r : ℝ)
    (hs : 0 ≤ s) (hsH : s ≤ H) (hB : 0 ≤ B) (hC : 0 ≤ C) (he : 0 ≤ e)
    (hdR : |dR| ≤ C * Real.sqrt e) (hr : |r| ≤ B * e) :
    |4 * s ^ 2 * dR - 4 * s * r| ≤ (2 * H ^ 2 * C + 4 * H * B) * (e + 1) := by
  have hH : 0 ≤ H := hs.trans hsH
  have hs2 : s ^ 2 ≤ H ^ 2 := by nlinarith
  have hsqrt : 2 * Real.sqrt e ≤ e + 1 := by
    nlinarith [sq_nonneg (Real.sqrt e - 1), Real.sq_sqrt he]
  have hgrad := mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ 2 * H ^ 2 * C by positivity)
  have hric := mul_le_mul_of_nonneg_left (show e ≤ e + 1 by linarith)
    (show 0 ≤ 4 * H * B by positivity)
  calc
    _ ≤ |4 * s ^ 2 * dR| + |4 * s * r| := abs_sub _ _
    _ = 4 * s ^ 2 * |dR| + 4 * s * |r| := by
      simp only [abs_mul, abs_of_nonneg (show 0 ≤ (4 : ℝ) by norm_num),
        abs_of_nonneg (sq_nonneg s), abs_of_nonneg hs]
    _ ≤ 4 * s ^ 2 * (C * Real.sqrt e) + 4 * s * (B * e) :=
      add_le_add (mul_le_mul_of_nonneg_left hdR (by positivity))
        (mul_le_mul_of_nonneg_left hr (by positivity))
    _ ≤ 4 * H ^ 2 * (C * Real.sqrt e) + 4 * H * (B * e) :=
      add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs2 (by norm_num))
          (by positivity))
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsH (by norm_num))
          (by positivity))
    _ ≤ _ := by nlinarith

theorem nonnegativeEnergy_exp_bound (e e' : ℝ → ℝ) (H A : ℝ)
    (hH : 0 ≤ H) (_hA : 0 ≤ A)
    (hc : ContinuousOn e (Set.Icc 0 H))
    (he : ∀ s ∈ Set.Icc 0 H, 0 ≤ e s)
    (hd : ∀ s ∈ Set.Ico 0 H, HasDerivAt e (e' s) s)
    (hbound : ∀ s ∈ Set.Ico 0 H, |e' s| ≤ A * (e s + 1)) :
    ∀ s ∈ Set.Icc 0 H, e s + 1 ≤ (e 0 + 1) * Real.exp (A * s) := by
  have hn : ∀ s ∈ Set.Icc 0 H, 0 ≤ e s + 1 :=
    fun s hs ↦ add_nonneg (he s hs) zero_le_one
  have h := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := fun s ↦ e s + 1) (f' := e') (a := 0) (b := H)
    (δ := e 0 + 1) (K := A) (ε := 0)
    (hc.add_const 1) (fun s hs ↦ ((hd s hs).add_const 1).hasDerivWithinAt)
    (by simp only [Real.norm_eq_abs, abs_of_nonneg (hn 0 ⟨le_rfl, hH⟩), le_refl])
    (fun s hs ↦ by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hn s ⟨hs.1, hs.2.le⟩), add_zero]
        using hbound s hs)
  intro s hs
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hn s hs), gronwallBound_ε0, sub_zero]
    using h s hs

end PoincareConjecture.Proofs.M09
