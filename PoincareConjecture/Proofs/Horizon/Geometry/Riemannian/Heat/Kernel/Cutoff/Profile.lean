import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul









set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

namespace Poincare.Analysis



theorem exists_radial_cutoff_profile :
    ∃ (χ : ℝ → ℝ) (A B C : ℝ), 0 < A ∧ 0 < B ∧ 0 < C ∧
      ContDiff ℝ ∞ χ ∧ Antitone χ ∧ (∀ r, χ r ∈ Icc 0 1) ∧
      (∀ r, r ≤ 1 → χ r = 1) ∧ (∀ r, 2 ≤ r → χ r = 0) ∧
      (∀ r, deriv χ r ^ 2 ≤ A * χ r) ∧
      (∀ r, -B ≤ deriv (deriv χ) r) ∧ (∀ r, -C ≤ deriv χ r) := by
  let ψ := fun r : ℝ => Real.smoothTransition (2 - r)
  have hψ : ContDiff ℝ ∞ ψ :=
    Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)
  have hψ0 (r : ℝ) : 0 ≤ ψ r := Real.smoothTransition.nonneg _
  have hψ1 (r : ℝ) : ψ r ≤ 1 := Real.smoothTransition.le_one _
  have hψone (r : ℝ) (hr : r ≤ 1) : ψ r = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  have hψzero (r : ℝ) (hr : 2 ≤ r) : ψ r = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  have hψanti : Antitone ψ := fun r s hrs =>
    Real.smoothTransition.monotone (by linarith)
  have hsupport : HasCompactSupport (deriv ψ) := by
    apply HasCompactSupport.intro' (K := Icc (1 : ℝ) 2) isCompact_Icc isClosed_Icc
    intro r hr
    simp only [mem_Icc, not_and_or, not_le] at hr
    rcases hr with hr | hr
    · have he : ψ =ᶠ[𝓝 r] fun _ => 1 := by
        filter_upwards [eventually_lt_nhds hr] with s hs
        exact hψone s hs.le
      rw [he.deriv_eq]
      simp
    · have he : ψ =ᶠ[𝓝 r] fun _ => 0 := by
        filter_upwards [eventually_gt_nhds hr] with s hs
        exact hψzero s hs.le
      rw [he.deriv_eq]
      simp
  obtain ⟨L, hL⟩ := hsupport.exists_bound_of_continuous (hψ.deriv' (n := ∞)).continuous
  let C := max 1 L
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hbound (r : ℝ) : |deriv ψ r| ≤ C := (hL r).trans (le_max_right _ _)
  let χ := fun r => ψ r ^ 2
  have hχ : ContDiff ℝ ∞ χ := hψ.pow 2
  have hderiv (r : ℝ) : deriv χ r = 2 * ψ r * deriv ψ r := by
    simpa only [χ, Pi.pow_def, Nat.cast_ofNat, Nat.reduceSub, pow_one] using
      ((hψ.differentiable (by simp) r).hasDerivAt.pow 2).deriv
  have hsχ : HasCompactSupport (deriv χ) := hsupport.mono' (by
    intro r hr
    contrapose! hr
    simp only [Function.mem_support, ne_eq, not_not] at hr ⊢
    simp [hderiv, image_eq_zero_of_notMem_tsupport hr])
  obtain ⟨L₂, hL₂⟩ := hsχ.deriv.exists_bound_of_continuous
    ((hχ.deriv' (n := ∞)).deriv' (n := ∞)).continuous
  refine ⟨χ, 4 * C ^ 2, max 1 L₂, 2 * C, by positivity,
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), by positivity, hχ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r s hrs
    exact pow_le_pow_left₀ (hψ0 s) (hψanti hrs) 2
  · intro r
    exact ⟨sq_nonneg _, by dsimp [χ]; nlinarith [hψ0 r, hψ1 r]⟩
  · intro r hr
    simp [χ, hψone r hr]
  · intro r hr
    simp [χ, hψzero r hr]
  · intro r
    rw [hderiv]
    have hd : deriv ψ r ^ 2 ≤ C ^ 2 := by
      have h := abs_le.mp (hbound r)
      nlinarith [mul_nonneg (show 0 ≤ C - deriv ψ r by linarith)
        (show 0 ≤ C + deriv ψ r by linarith)]
    dsimp [χ]
    nlinarith [mul_le_mul_of_nonneg_left hd (sq_nonneg (ψ r))]
  · intro r
    exact (neg_le_neg (le_max_right 1 L₂)).trans (abs_le.mp (hL₂ r)).1
  · intro r
    rw [hderiv]
    have hd := (abs_le.mp (hbound r)).1
    nlinarith [mul_nonneg (hψ0 r) (show 0 ≤ deriv ψ r + C by linarith),
      mul_nonneg hC.le (show 0 ≤ 1 - ψ r by linarith [hψ1 r])]

end Poincare.Analysis
