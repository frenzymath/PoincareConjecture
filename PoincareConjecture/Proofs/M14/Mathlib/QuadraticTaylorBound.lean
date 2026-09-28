import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.Convex

set_option autoImplicit false

open Set
open scoped NNReal

namespace PoincareConjecture.M14

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_sub_sub_linear_le_sq {S : Set E} {f : E → F}
    {f' : E → E →L[ℝ] F} {K : ℝ≥0} (hS : Convex ℝ S)
    (hf : ∀ z ∈ S, HasFDerivWithinAt f (f' z) S z)
    (hLip : LipschitzOnWith K f' S) {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    ‖f y - f x - f' x (y - x)‖ ≤ (K : ℝ) * ‖y - x‖ ^ 2 := by
  have hseg : segment ℝ x y ⊆ S := hS.segment_subset hx hy
  have hder : ∀ z ∈ segment ℝ x y,
      HasFDerivWithinAt (fun z => f z - f' x z) (f' z - f' x)
        (segment ℝ x y) z := by
    intro z hz
    exact ((hf z (hseg hz)).mono hseg).sub (f' x).hasFDerivAt.hasFDerivWithinAt
  have hbound : ∀ z ∈ segment ℝ x y,
      ‖f' z - f' x‖ ≤ (K : ℝ) * ‖y - x‖ := by
    intro z hz
    exact (hLip.norm_sub_le (hseg hz) hx).trans
      (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) K.coe_nonneg)
  have h := (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hder hbound (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [map_sub, sub_sub_sub_comm, mul_assoc, ← pow_two] using h

end PoincareConjecture.M14
