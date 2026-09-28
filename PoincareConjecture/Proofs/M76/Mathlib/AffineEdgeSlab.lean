import PoincareConjecture.Proofs.M76.Mathlib.AffineEdgeLevelUniqueness

set_option autoImplicit false

open Set

namespace AffineMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem injOn_edgeLine (A : E →ᵃ[ℝ] ℝ) {v u : E} (hu : A u ≠ A v) :
    InjOn A (affineSpan ℝ ({v, u} : Set E)) := by
  intro x hx y hy hxy
  exact (A.eq_edgeLevel_of_mem_affineSpan hu hx rfl).trans
    (A.eq_edgeLevel_of_mem_affineSpan hu hy hxy.symm).symm

theorem edgeLevel_mem_segment (A : E →ᵃ[ℝ] ℝ) {v u : E} {c : ℝ}
    (h : (A v < c ∧ c < A u) ∨ (A u < c ∧ c < A v)) :
    A.edgeLevel v u c ∈ segment ℝ v u := by
  rcases h with ⟨hv, hu⟩ | ⟨hu, hv⟩
  · exact openSegment_subset_segment ℝ v u (A.edgeLevel_mem_openSegment hv hu)
  · rw [← A.edgeLevel_reverse (ne_of_lt (hu.trans hv)) c, segment_symm ℝ v u]
    exact openSegment_subset_segment ℝ u v (A.edgeLevel_mem_openSegment hu hv)

end AffineMap
