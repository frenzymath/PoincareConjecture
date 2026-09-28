import PoincareConjecture.Definitions.Ch11.SingularLimits

set_option autoImplicit false

namespace PoincareConjecture

theorem four_lt_terminalAccuracyFactor : 4 < terminalAccuracyFactor := by
  unfold terminalAccuracyFactor; norm_num

theorem terminalAccuracyFactor_scalar_ratio_budget :
    (32 : ℝ) + 6 * (2000000000004 : ℝ) ^ 2 < terminalAccuracyFactor ^ 2 := by
  unfold terminalAccuracyFactor; norm_num

end PoincareConjecture
