import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set Metric

namespace NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def closedBallCompression (d : ℝ) (x : E) : E :=
  (d / (1 + (d - 1) * ‖x‖)) • x

omit [NormedSpace ℝ E] in
theorem closedBallCompression_denom_pos {d : ℝ} (hd : 0 < d)
    {x : E} (hx : ‖x‖ ≤ 1) : 0 < 1 + (d - 1) * ‖x‖ := by
  by_cases hx0 : ‖x‖ = 0
  · simp only [hx0, mul_zero, add_zero, zero_lt_one]
  · have hp := mul_pos hd (lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx0))
    nlinarith

theorem norm_closedBallCompression {d : ℝ} (hd : 0 < d)
    {x : E} (hx : ‖x‖ ≤ 1) :
    ‖closedBallCompression d x‖ = (d / (1 + (d - 1) * ‖x‖)) * ‖x‖ := by
  rw [closedBallCompression, norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos hd (closedBallCompression_denom_pos hd hx))]

theorem norm_closedBallCompression_le_one {d : ℝ} (hd : 0 < d)
    {x : E} (hx : ‖x‖ ≤ 1) : ‖closedBallCompression d x‖ ≤ 1 := by
  rw [norm_closedBallCompression hd hx, div_mul_eq_mul_div,
    div_le_iff₀ (closedBallCompression_denom_pos hd hx)]
  nlinarith

theorem closedBallCompression_of_norm_eq_one {d : ℝ} (hd : 0 < d)
    {x : E} (hx : ‖x‖ = 1) : closedBallCompression d x = x := by
  simp [closedBallCompression, hx, hd.ne']

theorem closedBallCompression_inv {d : ℝ} (hd : 0 < d)
    {x : E} (hx : ‖x‖ ≤ 1) :
    closedBallCompression d⁻¹ (closedBallCompression d x) = x := by
  have hden := (closedBallCompression_denom_pos hd hx).ne'
  have he : 1 + (d⁻¹ - 1) * ‖closedBallCompression d x‖ =
      (1 + (d - 1) * ‖x‖)⁻¹ := by
    rw [norm_closedBallCompression hd hx]
    field_simp [hden, hd.ne']
    ring
  rw [closedBallCompression, he, closedBallCompression, smul_smul]
  have hc : d⁻¹ / (1 + (d - 1) * ‖x‖)⁻¹ *
      (d / (1 + (d - 1) * ‖x‖)) = 1 := by
    field_simp [hden, hd.ne']
  rw [hc, one_smul]

theorem continuousOn_closedBallCompression {d : ℝ} (hd : 0 < d) :
    ContinuousOn (closedBallCompression d : E → E) (closedBall 0 1) := by
  apply ContinuousOn.smul _ continuousOn_id
  apply ContinuousOn.div continuousOn_const
    (continuousOn_const.add (continuousOn_const.mul continuous_norm.continuousOn))
  intro x hx
  exact (closedBallCompression_denom_pos hd (mem_closedBall_zero_iff.mp hx)).ne'

theorem norm_closedBallCompression_lt {r d η : ℝ} (hr : r < 1)
    (hd : 0 < d) (hη : 0 < η)
    (hdη : d ≤ η * (1 - r) / 2) {x : E} (hx : ‖x‖ ≤ r) :
    ‖closedBallCompression d x‖ < η := by
  have hx1 : ‖x‖ ≤ 1 := hx.trans hr.le
  have hden := closedBallCompression_denom_pos hd hx1
  have hdenlower : 1 - r ≤ 1 + (d - 1) * ‖x‖ := by
    have hp := mul_nonneg hd.le (norm_nonneg x)
    nlinarith
  have hn : d * ‖x‖ ≤ d := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hx1 hd.le
  rw [norm_closedBallCompression hd hx1, div_mul_eq_mul_div, div_lt_iff₀ hden]
  have hpos : 0 < η * (1 - r) := mul_pos hη (sub_pos.mpr hr)
  have hmul := mul_le_mul_of_nonneg_left hdenlower hη.le
  linarith

end NormedSpace

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def closedBallCompression (d : ℝ) (hd : 0 < d) :
    closedBall (0 : E) 1 ≃ₜ closedBall (0 : E) 1 where
  toFun x := ⟨NormedSpace.closedBallCompression d x,
    mem_closedBall_zero_iff.mpr (NormedSpace.norm_closedBallCompression_le_one hd
      (mem_closedBall_zero_iff.mp x.property))⟩
  invFun x := ⟨NormedSpace.closedBallCompression d⁻¹ x,
    mem_closedBall_zero_iff.mpr (NormedSpace.norm_closedBallCompression_le_one
      (inv_pos.mpr hd) (mem_closedBall_zero_iff.mp x.property))⟩
  left_inv x := Subtype.ext (NormedSpace.closedBallCompression_inv hd
    (mem_closedBall_zero_iff.mp x.property))
  right_inv x := Subtype.ext (by
    simpa only [inv_inv] using NormedSpace.closedBallCompression_inv (inv_pos.mpr hd)
      (mem_closedBall_zero_iff.mp x.property))
  continuous_toFun := (NormedSpace.continuousOn_closedBallCompression hd).domRestrict.codRestrict _
  continuous_invFun :=
    (NormedSpace.continuousOn_closedBallCompression (inv_pos.mpr hd)).domRestrict.codRestrict _

theorem closedBallCompression_apply_sphere (d : ℝ) (hd : 0 < d)
    (x : closedBall (0 : E) 1) (hx : (x : E) ∈ sphere 0 1) :
    closedBallCompression d hd x = x := by
  apply Subtype.ext
  exact NormedSpace.closedBallCompression_of_norm_eq_one hd
    (mem_sphere_zero_iff_norm.mp hx)

theorem exists_closedBallCompression {r η : ℝ} (hr : r < 1) (hη : 0 < η) :
    ∃ h : closedBall (0 : E) 1 ≃ₜ closedBall (0 : E) 1,
      (∀ x : closedBall (0 : E) 1, (x : E) ∈ sphere 0 1 → h x = x) ∧
      ∀ x : closedBall (0 : E) 1, ‖(x : E)‖ ≤ r → ‖(h x : E)‖ < η := by
  let d := min (1 / 2 : ℝ) (η * (1 - r) / 2)
  have hd : 0 < d := lt_min (by norm_num)
    (div_pos (mul_pos hη (sub_pos.mpr hr)) (by norm_num))
  refine ⟨closedBallCompression d hd, closedBallCompression_apply_sphere d hd, ?_⟩
  intro x hx
  exact NormedSpace.norm_closedBallCompression_lt hr hd hη (min_le_right _ _) hx

end Homeomorph
