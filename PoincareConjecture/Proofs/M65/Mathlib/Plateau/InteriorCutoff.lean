import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

set_option autoImplicit false

open Set Filter MeasureTheory MeasureTheory.Measure Metric
open scoped Topology ContDiff

namespace ContDiffBump

theorem exists_integral_sub_one_sq_lt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (mu : Measure E) [IsAddHaarMeasure mu] {eps : ℝ} (heps : 0 < eps) :
    ∃ theta : ContDiffBump (0 : E), theta.rOut < 1 ∧
      ∫ x in closedBall (0 : E) 1, (1 - theta x) ^ 2 ∂mu < eps := by
  let : IsFiniteMeasure (mu.restrict (closedBall (0 : E) 1)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : E) 1).measure_lt_top.ne
  let rho (n : ℕ) : ℝ := 1 - 1 / ((n : ℝ) + 2)
  have hrho (n : ℕ) : 0 < rho n ∧ rho n < 1 := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hpos : 0 < 1 / ((n : ℝ) + 2) := by positivity
    have hlt : 1 / ((n : ℝ) + 2) < 1 :=
      (div_lt_one (by positivity)).mpr (by linarith)
    dsimp only [rho]
    constructor <;> linarith
  let theta (n : ℕ) : ContDiffBump (0 : E) :=
    { rIn := rho n
      rOut := (rho n + 1) / 2
      rIn_pos := (hrho n).1
      rIn_lt_rOut := by linarith [(hrho n).2] }
  have hlim : Tendsto rho atTop (𝓝 1) := by
    have h := (tendsto_add_atTop_iff_nat 2).2
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [rho, Nat.cast_add, Nat.cast_ofNat, sub_zero] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub h
  have hball : ∀ᵐ x ∂(mu.restrict (closedBall (0 : E) 1)),
      x ∈ ball (0 : E) 1 := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall,
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp
        (addHaar_sphere_of_ne_zero mu (0 : E) one_ne_zero))] with x hx hxs
    rw [mem_closedBall] at hx
    rw [mem_sphere] at hxs
    exact hx.lt_of_ne hxs
  have hconv : ∀ᵐ x ∂(mu.restrict (closedBall (0 : E) 1)),
      Tendsto (fun n => (1 - theta n x) ^ 2) atTop (𝓝 0) := by
    filter_upwards [hball] with x hx
    have hlt : dist x 0 < 1 := hx
    have hev : ∀ᶠ n in atTop, dist x 0 < rho n :=
      hlim.eventually (lt_mem_nhds hlt)
    apply tendsto_const_nhds.congr'
    filter_upwards [hev] with n hn
    have heq : theta n x = 1 :=
      (theta n).one_of_mem_closedBall hn.le
    simp only [heq, sub_self, zero_pow (by decide : 2 ≠ 0)]
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (fun x => (1 - theta n x) ^ 2) (mu.restrict (closedBall (0 : E) 1)) :=
    ((continuous_const.sub (theta n).continuous).pow 2).aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ x ∂(mu.restrict (closedBall (0 : E) 1)),
      ‖(1 - theta n x) ^ 2‖ ≤ (1 : ℝ) := by
    filter_upwards [] with x
    have h0 := (theta n).nonneg (x := x)
    have h1 := (theta n).le_one (x := x)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith
  have hint := tendsto_integral_of_dominated_convergence
    (fun _ : E => (1 : ℝ)) hmeas (integrable_const 1) hbound hconv
  simp only [integral_zero] at hint
  obtain ⟨n, hn⟩ := (hint.eventually (gt_mem_nhds heps)).exists
  exact ⟨theta n, by dsimp only [theta]; linarith [(hrho n).2], hn⟩

end ContDiffBump
