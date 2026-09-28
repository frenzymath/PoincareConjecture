import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Basic

set_option autoImplicit false

open scoped BigOperators

theorem ContinuousLinearMap.sum_sq_euclidean_apply_le
    {E ι : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
    (L : E →L[ℝ] EuclideanSpace ℝ ι) {v : E} {b : ℝ} (hv : ‖v‖ ≤ b) :
    (∑ i, (L v i) ^ 2) ≤ (‖L‖ * b) ^ 2 := by
  apply (EuclideanSpace.real_norm_sq_eq (L v)).symm.trans_le
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  exact (L.le_opNorm v).trans (mul_le_mul_of_nonneg_left hv (norm_nonneg _))
