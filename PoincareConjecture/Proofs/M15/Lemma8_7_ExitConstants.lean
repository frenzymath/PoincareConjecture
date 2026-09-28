import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture.Proofs.M15

theorem exists_small_epsilon_exit_bounds (n : ℕ) (A : ℝ) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 2 ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon0 →
        Real.exp (2 * (n : ℝ) * epsilon) ≤ 4 / 3 ∧
        (2 / 3 : ℝ) * A * epsilon ^ 2 ≤ 1 / 16 := by
  have hf : ContinuousAt (fun e : ℝ => Real.exp (2 * (n : ℝ) * e)) 0 := by fun_prop
  have hg : ContinuousAt (fun e : ℝ => (2 / 3 : ℝ) * A * e ^ 2) 0 := by fun_prop
  have hf' : ∀ᶠ e : ℝ in 𝓝 0, Real.exp (2 * (n : ℝ) * e) < 4 / 3 :=
    hf (Iio_mem_nhds (by norm_num))
  have hg' : ∀ᶠ e : ℝ in 𝓝 0, (2 / 3 : ℝ) * A * e ^ 2 < 1 / 16 :=
    hg (Iio_mem_nhds (by norm_num))
  have hN := hf'.and hg'
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hN
  refine ⟨min (1 / 2) (delta / 2), lt_min (by norm_num) (half_pos hdelta),
    min_le_left _ _, ?_⟩
  intro epsilon hepsilon hepsilon0
  have hedelta : epsilon < delta :=
    (hepsilon0.trans (min_le_right _ _)).trans_lt (half_lt_self hdelta)
  have hmem : epsilon ∈ Metric.ball (0 : ℝ) delta := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hepsilon] using hedelta
  exact ⟨(hball hmem).1.le, (hball hmem).2.le⟩

theorem scaled_squareRoot_speed_le
    (n : ℕ) {A r epsilon q s : ℝ}
    (hA : 0 ≤ A) (hr : 0 < r) (hepsilon : 0 < epsilon)
    (hq0 : 0 ≤ q) (hq : q ≤ 1 / (4 * Real.sqrt epsilon))
    (hs0 : 0 ≤ s) (hs : s ≤ Real.sqrt epsilon * r)
    (hexp : Real.exp (2 * (n : ℝ) * epsilon) ≤ 4 / 3)
    (hAepsilon : (2 / 3 : ℝ) * A * epsilon ^ 2 ≤ 1 / 16) :
    Real.exp (2 * (n : ℝ) * (r⁻¹) ^ 2 * s ^ 2) *
      (q + (2 / 3 : ℝ) * (A / r ^ 3) * s ^ 3) ≤
        5 / (12 * Real.sqrt epsilon) := by
  have hw := Real.sqrt_pos.mpr hepsilon
  have hsquare : (r⁻¹) ^ 2 * s ^ 2 ≤ epsilon := by
    calc
      _ ≤ (r⁻¹) ^ 2 * (Real.sqrt epsilon * r) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs0 hs 2) (sq_nonneg _)
      _ = epsilon := by
        rw [mul_pow, Real.sq_sqrt hepsilon.le]
        field_simp
  have hexp' : Real.exp (2 * (n : ℝ) * (r⁻¹) ^ 2 * s ^ 2) ≤ 4 / 3 := by
    apply (Real.exp_le_exp.mpr ?_).trans hexp
    nlinarith only [mul_le_mul_of_nonneg_left hsquare
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg n))]
  have hq' : q * Real.sqrt epsilon ≤ 1 / 4 := by
    have h := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hw)).mp hq
    linarith
  have hterm : (2 / 3 : ℝ) * (A / r ^ 3) * s ^ 3 * Real.sqrt epsilon ≤ 1 / 16 := by
    calc
      _ ≤ (2 / 3 : ℝ) * (A / r ^ 3) * (Real.sqrt epsilon * r) ^ 3 *
          Real.sqrt epsilon :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs0 hs 3) (by positivity)) hw.le
      _ = (2 / 3 : ℝ) * A * epsilon ^ 2 := by
        calc
          _ = (2 / 3 : ℝ) * A * ((Real.sqrt epsilon) ^ 2) ^ 2 := by
            field_simp
          _ = _ := by rw [Real.sq_sqrt hepsilon.le]
      _ ≤ _ := hAepsilon
  have hpoly : 0 ≤ q + (2 / 3 : ℝ) * (A / r ^ 3) * s ^ 3 := by positivity
  apply (mul_le_mul_of_nonneg_right hexp' hpoly).trans
  apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 12) hw)).mpr
  nlinarith only [hq', hterm]

end PoincareConjecture.Proofs.M15
