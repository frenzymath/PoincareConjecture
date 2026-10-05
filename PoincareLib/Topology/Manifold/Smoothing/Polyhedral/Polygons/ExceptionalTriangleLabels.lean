import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.ExceptionalTriangleSlice

/-!
# Actual labels of nontrivial exceptional triangle sections

A triangle through the distinguished zero vertex whose section
is not a singleton has opposite-sign remaining vertices. These
are the labels used by the tapered collar construction. See
Alexander 1924, pp. 6--8 and M76 derivation 189.
-/

set_option autoImplicit false

open Set

namespace AffineMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]

/-- A nontrivial section through the only zero-height vertex
of a triangle supplies actual negative and positive remaining
vertex labels. Independence is not needed for this assertion.
See Alexander pp. 6--8 and M76 derivation 189. -/
theorem exists_exceptional_triangle_labels (A : E →ᵃ[ℝ] ℝ) {s : Finset E}
    (hs : s.card = 3) {q : E} (hqs : q ∈ s) (hq : A q = 0)
    (hreg : ∀ z ∈ s, z ≠ q → A z ≠ 0)
    (hnontriv : ∃ x ∈ convexHull ℝ (s : Set E) ∩ {x | A x = 0}, x ≠ q) :
    ∃ u v : E, s = {q, u, v} ∧ A u < 0 ∧ 0 < A v := by
  rcases A.exceptional_triangle_slice_eq_singleton_or_segment hs hqs hq hreg with h | h
  · obtain ⟨x, hx, hxq⟩ := hnontriv
    rw [h] at hx
    exact (hxq hx).elim
  · obtain ⟨he, _⟩ := h
    obtain ⟨u, v, hu, hv, hpair⟩ := he
    have heq : s.erase q = {u, v} := Finset.coe_injective (by
      simpa only [Finset.coe_pair] using hpair)
    refine ⟨u, v, ?_, hu, hv⟩
    rw [← heq, Finset.insert_erase hqs]

end AffineMap
