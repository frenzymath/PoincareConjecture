import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# The unique affine-zero crossing of an edge

An edge with endpoints on opposite sides of an affine zero
plane has one crossing point in its open segment. Uniqueness
holds on the entire affine line. See Alexander 1924, p. 6 and
M76 derivation 93.
-/

set_option autoImplicit false

open Set

namespace AffineMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The totalized affine zero-crossing formula on an ordered
pair of endpoints. Geometric use requires distinct endpoint
heights. See Alexander p. 6 and M76 derivation 93. -/
noncomputable def zeroCrossing (A : E →ᵃ[ℝ] ℝ) (u v : E) : E :=
  lineMap u v (-A u / (A v - A u))

/-- The crossing lies on the zero level when endpoint heights
differ. See Alexander p. 6 and M76 derivation 93. -/
theorem zeroCrossing_apply (A : E →ᵃ[ℝ] ℝ) {u v : E} (h : A u ≠ A v) :
    A (A.zeroCrossing u v) = 0 := by
  rw [zeroCrossing, apply_lineMap, lineMap_apply_ring']
  rw [div_mul_cancel₀ _ (sub_ne_zero.mpr h.symm), neg_add_cancel]

/-- Opposite strict signs put the zero crossing in the open
edge. See Alexander p. 6 and M76 derivation 93. -/
theorem zeroCrossing_mem_openSegment (A : E →ᵃ[ℝ] ℝ) {u v : E}
    (hu : A u < 0) (hv : 0 < A v) : A.zeroCrossing u v ∈ openSegment ℝ u v := by
  apply lineMap_mem_openSegment
  have hgap : 0 < A v - A u := by linarith
  exact ⟨div_pos (neg_pos.mpr hu) hgap, (div_lt_one hgap).mpr (by linarith)⟩

/-- A nonconstant affine height has at most one zero on an
affine line. See Alexander p. 6 and M76 derivation 93. -/
theorem eq_zeroCrossing_of_mem_affineSpan (A : E →ᵃ[ℝ] ℝ) {u v x : E}
    (h : A u ≠ A v) (hx : x ∈ affineSpan ℝ ({u, v} : Set E)) (hAx : A x = 0) :
    x = A.zeroCrossing u v := by
  obtain ⟨t, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hx
  rw [apply_lineMap, lineMap_apply_ring'] at hAx
  have ht : t = -A u / (A v - A u) := by
    apply (eq_div_iff (sub_ne_zero.mpr h.symm)).mpr
    linarith
  rw [zeroCrossing, ht]

/-- An edge with opposite strict endpoint signs meets the
zero level in precisely one point. See Alexander p. 6 and M76
derivation 93. -/
theorem convexHull_pair_inter_zero (A : E →ᵃ[ℝ] ℝ) {u v : E}
    (hu : A u < 0) (hv : 0 < A v) :
    convexHull ℝ ({u, v} : Set E) ∩ {x | A x = 0} = {A.zeroCrossing u v} := by
  have hne : A u ≠ A v := ne_of_lt (hu.trans hv)
  ext x
  constructor
  · intro hx
    exact A.eq_zeroCrossing_of_mem_affineSpan hne (convexHull_subset_affineSpan _ hx.1) hx.2
  · intro hx
    rw [mem_singleton_iff] at hx
    subst x
    refine ⟨?_, A.zeroCrossing_apply hne⟩
    rw [convexHull_pair]
    exact openSegment_subset_segment ℝ u v (A.zeroCrossing_mem_openSegment hu hv)

/-- A finite edge straddles the zero level if its endpoints
can be ordered with negative then positive height.
See Alexander p. 6 and M76 derivation 93. -/
def StraddlesZero (A : E →ᵃ[ℝ] ℝ) (e : Finset E) : Prop :=
  ∃ u v, A u < 0 ∧ 0 < A v ∧ (e : Set E) = {u, v}

/-- Every straddling edge has a unique actual zero point in
its geometric carrier. See Alexander p. 6 and M76 derivation 93. -/
theorem StraddlesZero.existsUnique (A : E →ᵃ[ℝ] ℝ) {e : Finset E}
    (he : A.StraddlesZero e) : ∃! x, x ∈ convexHull ℝ (e : Set E) ∧ A x = 0 := by
  obtain ⟨u, v, hu, hv, he⟩ := he
  have hset : convexHull ℝ (e : Set E) ∩ {x | A x = 0} = {A.zeroCrossing u v} := by
    rw [he]
    exact A.convexHull_pair_inter_zero hu hv
  refine ⟨A.zeroCrossing u v, ?_, ?_⟩
  · change A.zeroCrossing u v ∈ convexHull ℝ (e : Set E) ∩ {x | A x = 0}
    rw [hset]
    exact mem_singleton _
  · intro x hx
    exact mem_singleton_iff.mp (hset ▸ hx)

end AffineMap
