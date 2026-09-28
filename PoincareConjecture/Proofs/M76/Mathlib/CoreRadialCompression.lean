import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith












set_option autoImplicit false

open Set Metric

namespace NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



noncomputable def coreCompression (x : E) : E :=
  (2 / (1 + max 1 ‖x‖)) • x



noncomputable def coreExpansion (y : E) : E :=
  (2 - max 1 ‖y‖)⁻¹ • y



theorem coreCompression_of_norm_le_one {x : E} (hx : ‖x‖ ≤ 1) :
    coreCompression x = x := by
  norm_num [coreCompression, max_eq_left hx]



theorem coreCompression_of_one_le_norm {x : E} (hx : 1 ≤ ‖x‖) :
    coreCompression x = (2 / (1 + ‖x‖)) • x := by
  rw [coreCompression, max_eq_right hx]



theorem coreExpansion_of_norm_le_one {y : E} (hy : ‖y‖ ≤ 1) :
    coreExpansion y = y := by
  norm_num [coreExpansion, max_eq_left hy]




theorem coreExpansion_of_one_le_norm {y : E} (hy : 1 ≤ ‖y‖) :
    coreExpansion y = (2 - ‖y‖)⁻¹ • y := by
  rw [coreExpansion, max_eq_right hy]



theorem norm_coreCompression_lt_two (x : E) : ‖coreCompression x‖ < 2 := by
  by_cases hx : ‖x‖ ≤ 1
  · rw [coreCompression_of_norm_le_one hx]
    linarith
  · have hd : 0 < 1 + ‖x‖ := by positivity
    rw [coreCompression_of_one_le_norm (le_of_not_ge hx), norm_smul,
      Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) hd)]
    have he : (2 / (1 + ‖x‖)) * ‖x‖ = (2 * ‖x‖) / (1 + ‖x‖) := by ring
    rw [he]
    exact (div_lt_iff₀ hd).mpr (by linarith)

private theorem coreExpansion_compression (x : E) :
    coreExpansion (coreCompression x) = x := by
  by_cases hx : ‖x‖ ≤ 1
  · rw [coreCompression_of_norm_le_one hx, coreExpansion_of_norm_le_one hx]
  · have hr : 1 ≤ ‖x‖ := le_of_not_ge hx
    have hd : 0 < 1 + ‖x‖ := by positivity
    have hn : ‖coreCompression x‖ = (2 / (1 + ‖x‖)) * ‖x‖ := by
      rw [coreCompression_of_one_le_norm hr, norm_smul, Real.norm_eq_abs,
        abs_of_pos (div_pos (by norm_num) hd)]
    have hr' : 1 ≤ ‖coreCompression x‖ := by
      rw [hn]
      have he : (2 / (1 + ‖x‖)) * ‖x‖ = (2 * ‖x‖) / (1 + ‖x‖) := by ring
      rw [he]
      exact (le_div_iff₀ hd).mpr (by linarith)
    rw [coreExpansion_of_one_le_norm hr', hn, coreCompression_of_one_le_norm hr, smul_smul]
    have he : (2 - (2 / (1 + ‖x‖)) * ‖x‖)⁻¹ * (2 / (1 + ‖x‖)) = 1 := by
      have hd' : 2 - (2 / (1 + ‖x‖)) * ‖x‖ = 2 / (1 + ‖x‖) := by
        field_simp
        ring
      rw [hd', inv_mul_cancel₀ (div_ne_zero (by norm_num) hd.ne')]
    rw [he, one_smul]

private theorem coreCompression_expansion {y : E} (hy : ‖y‖ < 2) :
    coreCompression (coreExpansion y) = y := by
  by_cases hy1 : ‖y‖ ≤ 1
  · rw [coreExpansion_of_norm_le_one hy1, coreCompression_of_norm_le_one hy1]
  · have hr : 1 ≤ ‖y‖ := le_of_not_ge hy1
    have hd : 0 < 2 - ‖y‖ := sub_pos.mpr hy
    have hn : ‖coreExpansion y‖ = ‖y‖ / (2 - ‖y‖) := by
      rw [coreExpansion_of_one_le_norm hr, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hd), div_eq_inv_mul]
    have hr' : 1 ≤ ‖coreExpansion y‖ := by
      rw [hn]
      exact (le_div_iff₀ hd).mpr (by linarith)
    rw [coreCompression_of_one_le_norm hr', hn, coreExpansion_of_one_le_norm hr, smul_smul]
    have he : (2 / (1 + ‖y‖ / (2 - ‖y‖))) * (2 - ‖y‖)⁻¹ = 1 := by
      have hd' : 1 + ‖y‖ / (2 - ‖y‖) = 2 / (2 - ‖y‖) := by
        field_simp
        ring
      rw [hd']
      field_simp
    rw [he, one_smul]



theorem continuous_coreCompression : Continuous (coreCompression : E → E) := by
  change Continuous (fun x : E => (2 / (1 + max 1 ‖x‖)) • x)
  apply Continuous.smul _ continuous_id
  apply Continuous.div continuous_const
    (continuous_const.add (continuous_const.max continuous_norm))
  intro x
  change 1 + max 1 ‖x‖ ≠ 0
  have h := le_max_left (1 : ℝ) ‖x‖
  linarith



theorem continuousOn_coreExpansion : ContinuousOn (coreExpansion : E → E) (ball 0 2) := by
  apply ContinuousOn.smul _ continuousOn_id
  apply ContinuousOn.inv₀
    (continuousOn_const.sub (continuous_const.max continuous_norm).continuousOn)
  intro y hy
  have hnorm : ‖y‖ < 2 := mem_ball_zero_iff.mp hy
  exact (sub_pos.mpr (max_lt (by norm_num) hnorm)).ne'

end NormedSpace

namespace OpenPartialHomeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




noncomputable def coreCompression : OpenPartialHomeomorph E E where
  toFun := NormedSpace.coreCompression
  invFun := NormedSpace.coreExpansion
  source := univ
  target := ball 0 2
  map_source' x _ := mem_ball_zero_iff.mpr (NormedSpace.norm_coreCompression_lt_two x)
  map_target' _ _ := mem_univ _
  left_inv' x _ := NormedSpace.coreExpansion_compression x
  right_inv' _ hy := NormedSpace.coreCompression_expansion (mem_ball_zero_iff.mp hy)
  open_source := isOpen_univ
  open_target := isOpen_ball
  continuousOn_toFun := NormedSpace.continuous_coreCompression.continuousOn
  continuousOn_invFun := NormedSpace.continuousOn_coreExpansion

end OpenPartialHomeomorph
