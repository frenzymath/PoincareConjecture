import PoincareConjecture.Proofs.Horizon.Analysis.Measure.GaussianTails.Series
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Algebra.Order.Floor.Semiring



set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Poincare.Analysis

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {d : X → ℝ}

theorem lintegral_gaussian_le_of_sublevel_volume
    (hd : Measurable d) (hd0 : ∀ x, 0 ≤ d x)
    {n : ℕ} {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (hvol : ∀ m : ℕ, μ {x | d x < (m : ℝ) + 1} ≤
      ENNReal.ofReal (C * ((m : ℝ) + 1) ^ n)) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (-a * (d x) ^ 2)) ∂μ ≤
      ENNReal.ofReal (C * gaussianShellSum n a) := by
  let f : ℕ → X → ℝ≥0∞ := fun m => {x | d x < (m : ℝ) + 1}.indicator
    (fun _ => ENNReal.ofReal (Real.exp (-a * (m : ℝ) ^ 2)))
  have hmeas (m : ℕ) : Measurable (f m) :=
    measurable_const.indicator (measurableSet_lt hd measurable_const)
  have hbound (x : X) : ENNReal.ofReal (Real.exp (-a * (d x) ^ 2)) ≤ ∑' m, f m x := by
    apply le_trans _ (ENNReal.le_tsum (⌊d x⌋₊))
    dsimp only [f]
    rw [indicator_of_mem (s := {y | d y < (⌊d x⌋₊ : ℝ) + 1})
      (Nat.lt_floor_add_one (d x))]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left
      (sq_le_sq₀ (by positivity) (hd0 x) |>.mpr (Nat.floor_le (hd0 x))) (by linarith)
  calc
    (∫⁻ x, ENNReal.ofReal (Real.exp (-a * (d x) ^ 2)) ∂μ) ≤ ∫⁻ x, ∑' m, f m x ∂μ :=
      lintegral_mono hbound
    _ = ∑' m, ∫⁻ x, f m x ∂μ := lintegral_tsum (fun m => (hmeas m).aemeasurable)
    _ ≤ ∑' m : ℕ, ENNReal.ofReal (Real.exp (-a * (m : ℝ) ^ 2)) *
        ENNReal.ofReal (C * ((m : ℝ) + 1) ^ n) := by
      apply ENNReal.tsum_le_tsum
      intro m
      rw [lintegral_indicator (measurableSet_lt hd measurable_const)]
      simp only [lintegral_const, Measure.restrict_apply_univ]
      gcongr
      exact hvol m
    _ = ENNReal.ofReal (C * gaussianShellSum n a) := by
      simp_rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity)]
      · congr 1
        rw [gaussianShellSum, ← tsum_mul_left]
        apply tsum_congr
        intro m
        ring
      · convert! (summable_gaussian_shells n ha).mul_left C using 1
        ext m
        ring

theorem lintegral_gaussian_tail_le_of_sublevel_volume
    (hd : Measurable d) (hd0 : ∀ x, 0 ≤ d x)
    {n : ℕ} {a C R : ℝ} (ha : 0 < a) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hvol : ∀ m : ℕ, μ {x | d x < (m : ℝ) + 1} ≤
      ENNReal.ofReal (C * ((m : ℝ) + 1) ^ n)) :
    ∫⁻ x in {x | R ≤ d x}, ENNReal.ofReal (Real.exp (-a * (d x) ^ 2)) ∂μ ≤
      ENNReal.ofReal (Real.exp (-a / 2 * R ^ 2) * (C * gaussianShellSum n (a / 2))) := by
  rw [← lintegral_indicator (measurableSet_le measurable_const hd)]
  calc
    (∫⁻ x, {x | R ≤ d x}.indicator
        (fun x => ENNReal.ofReal (Real.exp (-a * (d x) ^ 2))) x ∂μ) ≤
        ∫⁻ x, ENNReal.ofReal (Real.exp (-a / 2 * R ^ 2)) *
          ENNReal.ofReal (Real.exp (-(a / 2) * (d x) ^ 2)) ∂μ := by
      apply lintegral_mono
      intro x
      dsimp only
      by_cases hx : R ≤ d x
      · rw [indicator_of_mem (s := {x | R ≤ d x}) hx,
          ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have hs : R ^ 2 ≤ (d x) ^ 2 := (sq_le_sq₀ hR (hd0 x)).mpr hx
        nlinarith
      · rw [indicator_of_notMem (s := {x | R ≤ d x}) hx]
        exact zero_le
    _ = ENNReal.ofReal (Real.exp (-a / 2 * R ^ 2)) *
        ∫⁻ x, ENNReal.ofReal (Real.exp (-(a / 2) * (d x) ^ 2)) ∂μ :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Real.exp (-a / 2 * R ^ 2)) *
        ENNReal.ofReal (C * gaussianShellSum n (a / 2)) := by
      gcongr
      exact lintegral_gaussian_le_of_sublevel_volume hd hd0
        (by linarith : 0 < a / 2) hC hvol
    _ = _ := (ENNReal.ofReal_mul (Real.exp_nonneg _)).symm

end Poincare.Analysis
