import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Matrix

namespace Poincare.LinearAlgebra

theorem crossProduct_dotProduct_self_of_orthonormal {u v : Fin 3 → ℝ}
    (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) (huv : u ⬝ᵥ v = 0) :
    (u ⨯₃ v) ⬝ᵥ (u ⨯₃ v) = 1 := by
  rw [cross_dot_cross, hu, hv, huv]
  ring

private theorem exists_unit_perpendicular (w : Fin 3 → ℝ) :
    ∃ u : Fin 3 → ℝ, u ⬝ᵥ u = 1 ∧ u ⬝ᵥ w = 0 := by
  by_cases hzero : w 0 = 0
  · refine ⟨![1, 0, 0], ?_, ?_⟩
    · norm_num [vec3_dotProduct]
    · simpa [vecHead] using hzero
  · let r : ℝ := Real.sqrt ((w 0) ^ 2 + (w 1) ^ 2)
    have hpos : 0 < (w 0) ^ 2 + (w 1) ^ 2 := by
      positivity
    have hr : r ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
    have hrsq : r ^ 2 = (w 0) ^ 2 + (w 1) ^ 2 :=
      Real.sq_sqrt hpos.le
    refine ⟨r⁻¹ • ![-w 1, w 0, 0], ?_, ?_⟩
    · simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul, vec3_dotProduct,
        cons_val_zero, cons_val_one, cons_val_two, vecHead, vecTail, Function.comp_apply,
        Fin.succ_zero_eq_one]
      field_simp
      nlinarith
    · simp only [smul_dotProduct, smul_eq_mul, vec3_dotProduct,
        cons_val_zero, cons_val_one, cons_val_two, vecHead, vecTail, Function.comp_apply,
        Fin.succ_zero_eq_one]
      ring

theorem exists_orthonormal_crossProduct_coordinates (w : Fin 3 → ℝ)
    (hw : w ⬝ᵥ w = 1) :
    ∃ u v : Fin 3 → ℝ,
      u ⬝ᵥ u = 1 ∧ v ⬝ᵥ v = 1 ∧ u ⬝ᵥ v = 0 ∧ u ⨯₃ v = w := by
  obtain ⟨u, hu, huw⟩ := exists_unit_perpendicular w
  have hwu : w ⬝ᵥ u = 0 := by rwa [dotProduct_comm]
  refine ⟨u, w ⨯₃ u, hu, ?_, dot_cross_self w u, ?_⟩
  · exact crossProduct_dotProduct_self_of_orthonormal hw hu hwu
  · rw [cross_cross_eq_smul_sub_smul', hu, hwu]
    simp

theorem exists_orthonormal_crossProduct (w : EuclideanSpace ℝ (Fin 3))
    (hw : dotProduct w w = 1) :
    ∃ u v : EuclideanSpace ℝ (Fin 3),
      dotProduct u u = 1 ∧ dotProduct v v = 1 ∧ dotProduct u v = 0 ∧
        crossProduct u v = (w : Fin 3 → ℝ) := by
  obtain ⟨u, v, hu, hv, huv, huv_eq⟩ := exists_orthonormal_crossProduct_coordinates w hw
  exact ⟨WithLp.toLp 2 u, WithLp.toLp 2 v, hu, hv, huv, huv_eq⟩

theorem exists_orthonormal_crossProduct_of_norm_eq_one (w : EuclideanSpace ℝ (Fin 3))
    (hw : ‖w‖ = 1) :
    ∃ u v : EuclideanSpace ℝ (Fin 3),
      dotProduct u u = 1 ∧ dotProduct v v = 1 ∧ dotProduct u v = 0 ∧
        crossProduct u v = (w : Fin 3 → ℝ) := by
  apply exists_orthonormal_crossProduct
  have h := real_inner_self_eq_norm_sq w
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, hw, one_pow] using h

theorem norm_crossProduct_of_orthonormal {u v : EuclideanSpace ℝ (Fin 3)}
    (hu : dotProduct u u = 1) (hv : dotProduct v v = 1) (huv : dotProduct u v = 0) :
    ‖(WithLp.toLp 2 (crossProduct u v) : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
  let w : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (crossProduct u v)
  have hdot : dotProduct w w = 1 := crossProduct_dotProduct_self_of_orthonormal hu hv huv
  have hsquare : ‖w‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    exact hdot
  nlinarith [norm_nonneg w]

end Poincare.LinearAlgebra
