import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace PoincareConjecture.Proofs.M58

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def twoVectorArea (u v : E) : ℝ :=
  Real.sqrt (max 0 (inner ℝ u u * inner ℝ v v - (inner ℝ u v) ^ 2))

theorem twoVectorArea_le (u v : E) : twoVectorArea u v ≤ ‖u‖ * ‖v‖ := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg (norm_nonneg _) (norm_nonneg _), ?_⟩
  rw [max_le_iff, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, mul_pow]
  exact ⟨mul_nonneg (sq_nonneg _) (sq_nonneg _), sub_le_self _ (sq_nonneg _)⟩

theorem twoVectorArea_change (u v : E) (a b c d : ℝ) :
    twoVectorArea (a • u + b • v) (c • u + d • v) =
      |a * d - b * c| * twoVectorArea u v := by
  have hgram : inner ℝ (a • u + b • v) (a • u + b • v) *
      inner ℝ (c • u + d • v) (c • u + d • v) -
      (inner ℝ (a • u + b • v) (c • u + d • v)) ^ 2 =
      (a * d - b * c) ^ 2 * (inner ℝ u u * inner ℝ v v - (inner ℝ u v) ^ 2) := by
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm v u]
    ring
  unfold twoVectorArea
  rw [hgram]
  have hmax := mul_max_of_nonneg 0
    (inner ℝ u u * inner ℝ v v - (inner ℝ u v) ^ 2) (sq_nonneg (a * d - b * c))
  rw [mul_zero] at hmax
  rw [← hmax]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

end PoincareConjecture.Proofs.M58
