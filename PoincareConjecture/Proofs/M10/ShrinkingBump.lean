import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

open Filter
open scoped Topology

namespace PoincareConjecture.M10

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def shrinkingBump (r : ℝ) (hr : 0 < r) (j : ℕ) : ContDiffBump (0 : E) where
  rIn := r / ((j : ℝ) + 1) / 2
  rOut := r / ((j : ℝ) + 1)
  rIn_pos := half_pos (div_pos hr (by positivity))
  rIn_lt_rOut := half_lt_self (div_pos hr (by positivity))

omit [NormedSpace ℝ E] in

theorem shrinkingBump_rOut_le (r : ℝ) (hr : 0 < r) (j : ℕ) :
    (shrinkingBump (E := E) r hr j).rOut ≤ r :=
  div_le_self hr.le (le_add_of_nonneg_left (Nat.cast_nonneg j))

omit [NormedSpace ℝ E] in

theorem shrinkingBump_rOut_tendsto (r : ℝ) (hr : 0 < r) :
    Tendsto (fun j ↦ (shrinkingBump (E := E) r hr j).rOut) atTop (𝓝 0) := by
  simpa only [shrinkingBump, one_div, div_eq_mul_inv, mul_zero, one_mul] using
    (tendsto_const_nhds (x := r)).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

end PoincareConjecture.M10
