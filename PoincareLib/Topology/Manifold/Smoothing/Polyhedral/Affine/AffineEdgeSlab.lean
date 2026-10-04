import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.AffineEdgeLevelUniqueness

/-!
# Crossing-edge height injectivity and slab membership

The affine height is injective on each crossing-edge line,
and its level points lie on the actual edge for either
orientation. See Alexander 1924, pp. 6--8 and M76 derivation 163.
-/

set_option autoImplicit false

open Set

namespace AffineMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Different endpoint heights make affine height injective
on the entire edge line. See M76 derivation 163. -/
theorem injOn_edgeLine (A : E →ᵃ[ℝ] ℝ) {v u : E} (hu : A u ≠ A v) :
    InjOn A (affineSpan ℝ ({v, u} : Set E)) := by
  intro x hx y hy hxy
  exact (A.eq_edgeLevel_of_mem_affineSpan hu hx rfl).trans
    (A.eq_edgeLevel_of_mem_affineSpan hu hy hxy.symm).symm

/-- Either strict ordering of the endpoint heights places
the prescribed intermediate point on the actual closed edge.
See Alexander p. 6 and M76 derivation 163. -/
theorem edgeLevel_mem_segment (A : E →ᵃ[ℝ] ℝ) {v u : E} {c : ℝ}
    (h : (A v < c ∧ c < A u) ∨ (A u < c ∧ c < A v)) :
    A.edgeLevel v u c ∈ segment ℝ v u := by
  rcases h with ⟨hv, hu⟩ | ⟨hu, hv⟩
  · exact openSegment_subset_segment ℝ v u (A.edgeLevel_mem_openSegment hv hu)
  · rw [← A.edgeLevel_reverse (ne_of_lt (hu.trans hv)) c, segment_symm ℝ v u]
    exact openSegment_subset_segment ℝ u v (A.edgeLevel_mem_openSegment hu hv)

end AffineMap
