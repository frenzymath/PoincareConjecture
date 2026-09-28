import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionFrontier
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

open Set Metric

namespace Set

theorem IsOpen.eq_empty_of_bounded_frontier_subset_cylinder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {κ : Type*} [Fintype κ] [Nonempty κ]
    {A : Set E} (hA : interior A = ∅)
    {U : Set (E × (κ → ℝ))} (hU : IsOpen U)
    (hb : Bornology.IsBounded U) (hfront : frontier U ⊆ A ×ˢ univ) :
    U = ∅ := by
  classical
  by_contra hne
  have hnot : ¬ U ⊆ A ×ˢ univ := by
    intro hsub
    have hi := interior_mono hsub
    rw [hU.interior_eq, interior_prod_eq, hA, empty_prod] at hi
    exact hne (subset_empty_iff.mp hi)
  obtain ⟨x, hx, hxA⟩ := not_subset.mp hnot
  have hxnot : x.1 ∉ A := fun h => hxA ⟨h, mem_univ _⟩
  let f : ℝ → E × (κ → ℝ) := fun t => (x.1, fun j => x.2 j + t)
  have hf : Continuous f := by fun_prop
  have hconn : IsPreconnected (range f) := isPreconnected_range hf
  have hdis : Disjoint (frontier U) (range f) := by
    apply disjoint_left.mpr
    rintro y hy ⟨t, rfl⟩
    exact hxnot (hfront hy).1
  have hsub : range f ⊆ U := hconn.m76_subset_of_disjoint_frontier hU hdis
    ⟨x, ⟨0, by ext <;> simp [f]⟩, hx⟩
  obtain ⟨r, hr⟩ := hb.subset_closedBall 0
  let j : κ := Classical.choice inferInstance
  have hnorm : ‖f (r + 1 - x.2 j)‖ ≤ r := by
    simpa only [mem_closedBall, dist_zero_right] using
      hr (hsub (mem_range_self (r + 1 - x.2 j)))
  have hcoord := (norm_le_pi_norm (f (r + 1 - x.2 j)).2 j).trans
    ((norm_snd_le (f (r + 1 - x.2 j))).trans hnorm)
  change |x.2 j + (r + 1 - x.2 j)| ≤ r at hcoord
  have := le_abs_self (x.2 j + (r + 1 - x.2 j))
  linarith

end Set
