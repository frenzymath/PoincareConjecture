import PoincareConjecture.Proofs.M76.Mathlib.ExceptionalTriangleSlice

set_option autoImplicit false

open Set

namespace AffineMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]

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
