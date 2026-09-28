import PoincareConjecture.Proofs.M76.Mathlib.AffineEdgeLevel

set_option autoImplicit false

open Set

namespace AffineMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]

theorem exists_regular_triangle_apex (A : E →ᵃ[ℝ] ℝ) {s : Finset E} (hs : s.card = 3)
    {α β : ℝ} (hreg : ∀ z ∈ s, A z < α ∨ β < A z)
    (hmeet : (convexHull ℝ (s : Set E) ∩ {x | A x ∈ Icc α β}).Nonempty) :
    ∃ v u w, s = {v, u, w} ∧ v ≠ u ∧ v ≠ w ∧ u ≠ w ∧
      ((A v < α ∧ β < A u ∧ β < A w) ∨ (β < A v ∧ A u < α ∧ A w < α)) := by
  classical
  obtain ⟨x, hx, hAx⟩ := hmeet
  have hnotlow : ¬ ∀ z ∈ s, A z < α := by
    intro h
    exact (not_lt_of_ge hAx.1)
      (convexHull_min h ((convex_Iio α).affine_preimage A) hx)
  have hnothigh : ¬ ∀ z ∈ s, β < A z := by
    intro h
    exact (not_lt_of_ge hAx.2)
      (convexHull_min h ((convex_Ioi β).affine_preimage A) hx)
  obtain ⟨v, u, w, hvu, hvw, huw, rfl⟩ := Finset.card_eq_three.mp hs
  have hrotate : ({v, u, w} : Finset E) = {w, v, u} := by
    ext z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hswap : ({v, u, w} : Finset E) = {u, v, w} := by
    ext z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  rcases hreg v (by simp) with hv | hv <;>
    rcases hreg u (by simp) with hu | hu <;>
    rcases hreg w (by simp) with hw | hw
  · exfalso
    apply hnotlow
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> assumption
  · exact ⟨w, v, u, hrotate, hvw.symm, huw.symm, hvu, Or.inr ⟨hw, hv, hu⟩⟩
  · exact ⟨u, v, w, hswap, hvu.symm, huw, hvw, Or.inr ⟨hu, hv, hw⟩⟩
  · exact ⟨v, u, w, rfl, hvu, hvw, huw, Or.inl ⟨hv, hu, hw⟩⟩
  · exact ⟨v, u, w, rfl, hvu, hvw, huw, Or.inr ⟨hv, hu, hw⟩⟩
  · exact ⟨u, v, w, hswap, hvu.symm, huw, hvw, Or.inl ⟨hu, hv, hw⟩⟩
  · exact ⟨w, v, u, hrotate, hvw.symm, huw.symm, hvu, Or.inl ⟨hw, hv, hu⟩⟩
  · exfalso
    apply hnothigh
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> assumption

end AffineMap

namespace Finset

theorem eq_pair_of_subset_triple {V : Type*} [DecidableEq V] {e : Finset V}
    (he : e.card = 2) {v u w : V} (hes : e ⊆ {v, u, w}) :
    e = {v, u} ∨ e = {v, w} ∨ e = {u, w} := by
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp he
  have ha : a = v ∨ a = u ∨ a = w := by
    simpa only [mem_insert, mem_singleton] using hes (mem_insert_self a {b})
  have hb : b = v ∨ b = u ∨ b = w := by
    simpa only [mem_insert, mem_singleton] using hes (mem_insert_of_mem (mem_singleton_self b))
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    simp_all only [ne_eq, not_true_eq_false, pair_comm, true_or, or_true]

end Finset
