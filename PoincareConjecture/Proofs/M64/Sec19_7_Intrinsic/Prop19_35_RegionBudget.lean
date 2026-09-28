import PoincareConjecture.Statements.M64Comparison

set_option autoImplicit false

namespace PoincareConjecture

theorem m64Intrinsic_region_budget_contradiction
    {K mu delta area curvature turning : ℝ}
    (harea : area < mu)
    (hcurvature : Real.pi / 2 - turning ≤ curvature)
    (hupper : curvature ≤ max K 0 * area)
    (hturning : turning < delta)
    (hbudget : max K 0 * mu + delta ≤ Real.pi / 2) :
    False := by
  have hscale : max K 0 * area ≤ max K 0 * mu := by
    exact mul_le_mul_of_nonneg_left harea.le (le_max_right K 0)
  linarith

end PoincareConjecture
