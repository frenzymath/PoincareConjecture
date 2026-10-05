import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A fixed sequence of normalized smooth kernels

The outer radii are r/(j+1), with positive half-sized inner radii.
They stay within the chart margin and tend to zero.
-/

set_option autoImplicit false

open Filter
open scoped Topology

namespace PoincareMT.ReducedVolume

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A shrinking bump with a fixed positive spatial margin. -/
noncomputable def shrinkingBump (r : ℝ) (hr : 0 < r) (j : ℕ) : ContDiffBump (0 : E) where
  rIn := r / ((j : ℝ) + 1) / 2
  rOut := r / ((j : ℝ) + 1)
  rIn_pos := half_pos (div_pos hr (by positivity))
  rIn_lt_rOut := half_lt_self (div_pos hr (by positivity))

omit [NormedSpace ℝ E] in
/-- Each kernel remains within the original positive margin. -/
theorem shrinkingBump_rOut_le (r : ℝ) (hr : 0 < r) (j : ℕ) :
    (shrinkingBump (E := E) r hr j).rOut ≤ r :=
  div_le_self hr.le (le_add_of_nonneg_left (Nat.cast_nonneg j))

omit [NormedSpace ℝ E] in
/-- The explicitly chosen radii tend to zero. -/
theorem shrinkingBump_rOut_tendsto (r : ℝ) (hr : 0 < r) :
    Tendsto (fun j ↦ (shrinkingBump (E := E) r hr j).rOut) atTop (𝓝 0) := by
  simpa only [shrinkingBump, one_div, div_eq_mul_inv, mul_zero, one_mul] using
    (tendsto_const_nhds (x := r)).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

end PoincareMT.ReducedVolume
