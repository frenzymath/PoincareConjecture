import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Poincare

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem radial_cross_norm_sq (x u v : E) :
    ‖inner ℝ x u • v - inner ℝ x v • u‖ ^ 2 =
      inner ℝ x u ^ 2 * inner ℝ v v + inner ℝ x v ^ 2 * inner ℝ u u -
        2 * inner ℝ x u * inner ℝ x v * inner ℝ u v := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm u v]
  ring

theorem radial_gram_nonneg {x : E} (hx : x ≠ 0) (u v : E) :
    0 ≤ inner ℝ u u * inner ℝ v v - inner ℝ u v ^ 2 -
      ‖inner ℝ x u • v - inner ℝ x v • u‖ ^ 2 / ‖x‖ ^ 2 := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  let U := u - (inner ℝ x u / ‖x‖ ^ 2) • x
  let V := v - (inner ℝ x v / ‖x‖ ^ 2) • x
  have hi : inner ℝ U U * inner ℝ V V - inner ℝ U V ^ 2 =
      inner ℝ u u * inner ℝ v v - inner ℝ u v ^ 2 -
        ‖inner ℝ x u • v - inner ℝ x v • u‖ ^ 2 / ‖x‖ ^ 2 := by
    rw [radial_cross_norm_sq]
    dsimp only [U, V]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_self_eq_norm_sq x]
    rw [real_inner_comm x u, real_inner_comm x v]
    field_simp
    ring
  rw [← hi]
  nlinarith only [real_inner_mul_inner_self_le U V]

theorem radial_pairing_gram (c b : ℝ) (x u v : E) :
    (c * inner ℝ u u + b * (inner ℝ x u * inner ℝ x u)) *
        (c * inner ℝ v v + b * (inner ℝ x v * inner ℝ x v)) -
      (c * inner ℝ u v + b * (inner ℝ x u * inner ℝ x v)) ^ 2 =
      c ^ 2 * (inner ℝ u u * inner ℝ v v - inner ℝ u v ^ 2) +
        c * b * ‖inner ℝ x u • v - inner ℝ x v • u‖ ^ 2 := by
  rw [radial_cross_norm_sq]
  ring

end Poincare
