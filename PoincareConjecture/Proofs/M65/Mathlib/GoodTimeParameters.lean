import PoincareConjecture.Proofs.M65.Mathlib.FineGrid
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt








set_option autoImplicit false

namespace PoincareConjecture.M65




theorem exists_goodTime_grid_parameters {a b C delta ell d K : ℝ}
    (hab : a < b) (hdelta : 0 < delta) (hell : 0 < ell) (hd : 0 < d) (hK : 0 ≤ K) :
    ∃ B : ℝ, 1 < B ∧ ∃ T : ℝ, T ∈ Set.Ioo a b ∧ Real.exp (K * (b - T)) < 4 / 3 ∧
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧ r ≤ ell * Real.exp (-K * (b - a)) ∧
        r * B ≤ d ^ 2 ∧ T + d * r ^ 2 < b ∧
        ∃ n : ℕ, ∃ step : ℝ, 0 < step ∧ a + ((n : ℝ) + 2) * step = T ∧
          4 * step ≤ d * r ^ 2 ∧ C / B + 2 * step + (b - T) < delta := by
  let logGrowth := Real.log (4 / 3 : ℝ)
  have hlog : 0 < logGrowth := Real.log_pos (by norm_num)
  have htime : 0 < b - a := sub_pos.mpr hab
  have htermTime : 0 < 2 / (b - a) := div_pos (by norm_num) htime
  have htermGap : 0 < 4 * (|C| + 1) / delta := by positivity
  have htermGrowth : 0 ≤ 2 * K / logGrowth := by positivity
  let B := 2 + 2 / (b - a) + 4 * (|C| + 1) / delta + 2 * K / logGrowth
  have hB1 : 1 < B := by dsimp [B]; linarith
  have hB : 0 < B := by linarith
  have hBtime : 2 / (b - a) < B := by dsimp [B]; linarith
  have hBgap : 4 * (|C| + 1) / delta < B := by dsimp [B]; linarith
  have hBgrowth : 2 * K / logGrowth < B := by dsimp [B]; linarith
  have hshort : 1 / B < b - a := by
    apply (div_lt_iff₀ hB).mpr
    have h := (div_lt_iff₀ htime).mp hBtime
    linarith
  have hKB : K / B < logGrowth := by
    apply (div_lt_iff₀ hB).mpr
    have h := (div_lt_iff₀ hlog).mp hBgrowth
    nlinarith
  have hgap : (C + 1) / B < delta / 4 := by
    apply (div_lt_iff₀ hB).mpr
    have h := (div_lt_iff₀ hdelta).mp hBgap
    nlinarith [le_abs_self C]
  let T := b - 1 / B
  have hT : T ∈ Set.Ioo a b :=
    ⟨by dsimp [T]; linarith, by dsimp [T]; linarith [one_div_pos.mpr hB]⟩
  have hgrowth : Real.exp (K * (b - T)) < 4 / 3 := by
    have heq : K * (b - T) = K / B := by dsimp [T]; ring
    rw [heq]
    calc
      _ < Real.exp logGrowth := Real.exp_lt_exp.mpr hKB
      _ = 4 / 3 := Real.exp_log (by norm_num)
  let q := ell * Real.exp (-K * (b - a))
  have hq : 0 < q := mul_pos hell (Real.exp_pos _)
  let root := Real.sqrt (1 / (2 * B * d))
  have hroot : 0 < root := Real.sqrt_pos.mpr (by positivity)
  let r := min (1 / 2 : ℝ) (min (q / 2) (min (d ^ 2 / (2 * B)) root))
  have hr : 0 < r := by dsimp [r]; positivity
  have hrhalf : r ≤ 1 / 2 := min_le_left _ _
  have hrq : r ≤ q / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hrtail : r ≤ min (d ^ 2 / (2 * B)) root :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hrB : r * B ≤ d ^ 2 := by
    have h := (le_div_iff₀ (mul_pos (by norm_num) hB)).mp
      (hrtail.trans (min_le_left _ _))
    nlinarith [sq_nonneg d]
  have hrsq : r ^ 2 ≤ 1 / (2 * B * d) := by
    have hsq := pow_le_pow_left₀ hr.le (hrtail.trans (min_le_right _ _)) 2
    rwa [show root ^ 2 = 1 / (2 * B * d) from Real.sq_sqrt (by positivity)] at hsq
  have hwidth : d * r ^ 2 ≤ 1 / (2 * B) := by
    calc
      _ ≤ d * (1 / (2 * B * d)) := mul_le_mul_of_nonneg_left hrsq hd.le
      _ = _ := by field_simp
  have hhalf : 1 / (2 * B) < 1 / B := by
    rw [one_div, one_div]
    exact (inv_lt_inv₀ (mul_pos (by norm_num) hB) hB).mpr (by linarith)
  have hwindow : T + d * r ^ 2 < b := by dsimp [T]; linarith
  have hsmall : 0 < min (d * r ^ 2 / 4) (delta / 8) := by positivity
  obtain ⟨n, step, hstep, hstepSmall, hend⟩ := exists_positive_grid_step hT.1 hsmall
  have hstepWidth := hstepSmall.trans_le (min_le_left _ _)
  have hstepGap := hstepSmall.trans_le (min_le_right _ _)
  refine ⟨B, hB1, T, hT, hgrowth, r, hr, by linarith, by change r ≤ q; linarith,
    hrB, hwindow, n, step, hstep, hend, by linarith, ?_⟩
  have hsum : C / B + (b - T) = (C + 1) / B := by dsimp [T]; ring
  calc
    C / B + 2 * step + (b - T) = (C + 1) / B + 2 * step := by rw [← hsum]; ring
    _ < delta := by linarith

end PoincareConjecture.M65
