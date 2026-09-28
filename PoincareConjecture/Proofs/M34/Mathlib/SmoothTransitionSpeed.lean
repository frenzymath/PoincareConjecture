import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

namespace Real.smoothTransition

theorem exists_deriv_bound : ∃ C : ℝ, 1 ≤ C ∧ ∀ x : ℝ,
    |deriv Real.smoothTransition x| ≤ C := by
  have hcont : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).continuous_deriv (by simp)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max 1 C, le_max_left _ _, fun x => ?_⟩
  by_cases hx : x ∈ Icc (-1 : ℝ) 2
  · exact (hC x hx).trans (le_max_right _ _)
  have hzero : deriv Real.smoothTransition x = 0 := by
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · apply HasDerivAt.deriv
      apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds (show x < 0 by linarith)] with y hy
      exact zero_of_nonpos hy.le
    · apply HasDerivAt.deriv
      apply (hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds (show 1 < x by linarith)] with y hy
      exact one_of_one_le hy.le
  rw [hzero, abs_zero]
  exact zero_le_one.trans (le_max_left _ _)

end Real.smoothTransition
