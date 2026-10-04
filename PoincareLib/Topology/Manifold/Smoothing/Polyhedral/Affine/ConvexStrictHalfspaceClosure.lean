import Mathlib.Analysis.Convex.Topology

/-!
# Closure of a nonempty strict affine side in a convex set

In a closed convex set of nonpositive height, one negative point
makes the strict-negative subset dense. This identifies the
protected negative part in Alexander's deformation, pp. 7--8;
see M76 derivation 155.
-/

set_option autoImplicit false

open Set

namespace Convex

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [Module ℝ E] [ContinuousSMul ℝ E]

/-- If an affine function is nonpositive on a closed convex
set and negative somewhere there, its strictly negative part
is dense in that set. See M76 derivation 155. -/
theorem closure_inter_affine_neg {C : Set E} (hcv : Convex ℝ C) (hC : IsClosed C)
    (A : E →ᵃ[ℝ] ℝ) (hA : ∀ x ∈ C, A x ≤ 0)
    (hne : (C ∩ {x | A x < 0}).Nonempty) :
    closure (C ∩ {x | A x < 0}) = C := by
  apply Subset.antisymm (closure_minimal inter_subset_left hC)
  obtain ⟨y, hyC, hyA⟩ := hne
  intro x hx
  have hseg : openSegment ℝ x y ⊆ C ∩ {z | A z < 0} := by
    rintro z ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨hcv hx hyC ha.le hb.le hab, ?_⟩
    change A (a • x + b • y) < 0
    rw [Convex.combo_affine_apply hab]
    exact add_neg_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos ha.le (hA x hx))
      (mul_neg_of_pos_of_neg hb hyA)
  exact closure_mono hseg (segment_subset_closure_openSegment (left_mem_segment ℝ x y))

end Convex
