import PoincareConjecture.Definitions.Ch18.LoopSpaceWidth
import Mathlib.Topology.UnitInterval

set_option autoImplicit false

namespace PoincareConjecture.M65

noncomputable def sphereHeight : ContinuousMap LoopTwoSphere unitInterval where
  toFun z := ⟨(z.1 0 + 1) / 2, by
    have h := PiLp.norm_apply_le z.1 0
    rw [z.2, Real.norm_eq_abs] at h
    obtain ⟨hl, hu⟩ := abs_le.mp h
    constructor <;> linarith⟩
  continuous_toFun := by fun_prop

noncomputable def sphereHeightSection : ContinuousMap unitInterval LoopTwoSphere where
  toFun u := ⟨!₂[2 * (u : ℝ) - 1, Real.sqrt (1 - (2 * (u : ℝ) - 1) ^ 2), 0], by
    have hnonneg : 0 ≤ 1 - (2 * (u : ℝ) - 1) ^ 2 := by
      nlinarith [u.2.1, u.2.2]
    have hsqrt := Real.sq_sqrt hnonneg
    have hnorm := EuclideanSpace.real_norm_sq_eq
      !₂[2 * (u : ℝ) - 1, Real.sqrt (1 - (2 * (u : ℝ) - 1) ^ 2), 0]
    rw [Fin.sum_univ_three] at hnorm
    change ‖(!₂[2 * (u : ℝ) - 1, Real.sqrt (1 - (2 * (u : ℝ) - 1) ^ 2), 0] :
      LoopAmbient)‖ ^ 2 = (2 * (u : ℝ) - 1) ^ 2 +
        Real.sqrt (1 - (2 * (u : ℝ) - 1) ^ 2) ^ 2 + 0 ^ 2 at hnorm
    rw [hsqrt] at hnorm
    nlinarith [norm_nonneg
      (!₂[2 * (u : ℝ) - 1, Real.sqrt (1 - (2 * (u : ℝ) - 1) ^ 2), 0] : LoopAmbient)]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop

@[simp] theorem sphereHeight_section (u : unitInterval) :
    sphereHeight (sphereHeightSection u) = u := by
  apply Subtype.ext
  change ((2 * (u : ℝ) - 1) + 1) / 2 = u
  ring

end PoincareConjecture.M65
