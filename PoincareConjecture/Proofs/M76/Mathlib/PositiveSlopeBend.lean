import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring









set_option autoImplicit false

namespace PLStrip



def bend (a b x : ℝ) : ℝ := a * min x 0 + b * max x 0



theorem bend_of_nonpos (a b : ℝ) {x : ℝ} (hx : x ≤ 0) : bend a b x = a * x := by
  simp [bend, min_eq_left hx, max_eq_right hx]



theorem bend_of_nonneg (a b : ℝ) {x : ℝ} (hx : 0 ≤ x) : bend a b x = b * x := by
  simp [bend, min_eq_right hx, max_eq_left hx]



theorem continuous_bend (a b : ℝ) : Continuous (bend a b) :=
  (continuous_const.mul (continuous_id.min continuous_const)).add
    (continuous_const.mul (continuous_id.max continuous_const))



theorem strictMono_bend {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    StrictMono (bend a b) := by
  intro x y hxy
  by_cases hy : y ≤ 0
  · rw [bend_of_nonpos a b (hxy.le.trans hy), bend_of_nonpos a b hy]
    exact mul_lt_mul_of_pos_left hxy ha
  · by_cases hx : 0 ≤ x
    · rw [bend_of_nonneg a b hx, bend_of_nonneg a b (hx.trans hxy.le)]
      exact mul_lt_mul_of_pos_left hxy hb
    · rw [bend_of_nonpos a b (le_of_not_ge hx), bend_of_nonneg a b (le_of_not_ge hy)]
      exact lt_trans (mul_neg_of_pos_of_neg ha (lt_of_not_ge hx))
        (mul_pos hb (lt_of_not_ge hy))



theorem bend_inv_bend {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    bend a⁻¹ b⁻¹ (bend a b x) = x := by
  by_cases hx : x ≤ 0
  · rw [bend_of_nonpos a b hx,
      bend_of_nonpos a⁻¹ b⁻¹ (mul_nonpos_of_nonneg_of_nonpos ha.le hx)]
    simp [ha.ne']
  · have hx' : 0 ≤ x := le_of_not_ge hx
    rw [bend_of_nonneg a b hx', bend_of_nonneg a⁻¹ b⁻¹ (mul_nonneg hb.le hx')]
    simp [hb.ne']




noncomputable def bendHomeomorph {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : ℝ ≃ₜ ℝ where
  toFun := bend a b
  invFun := bend a⁻¹ b⁻¹
  left_inv := bend_inv_bend ha hb
  right_inv x := by
    simpa only [inv_inv] using bend_inv_bend (inv_pos.mpr ha) (inv_pos.mpr hb) x
  continuous_toFun := continuous_bend a b
  continuous_invFun := continuous_bend a⁻¹ b⁻¹

end PLStrip
