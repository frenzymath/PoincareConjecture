import PoincareConjecture.Proofs.M76.Mathlib.LocalRegionSideIncidence
import Mathlib.Analysis.Convex.Topology

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

theorem halfspace_of_convex_linear_frontier_chart
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D : Set X} (hD : IsClosed D) (hreg : closure (interior D) = D)
    {p : X} (hp : p ∈ frontier D) (H : OpenPartialHomeomorph X E)
    (hpH : p ∈ H.source) (ell : E →L[ℝ] ℝ) (hcv : Convex ℝ H.target)
    (hfront : ∀ x ∈ H.source, x ∈ frontier D ↔ ell (H x) = 0) :
    (∀ x ∈ H.source, x ∈ D ↔ 0 ≤ ell (H x)) ∨
      (∀ x ∈ H.source, x ∈ D ↔ ell (H x) ≤ 0) := by
  let P := H.symm '' (H.target ∩ ell ⁻¹' Ioi 0)
  let N := H.symm '' (H.target ∩ ell ⁻¹' Iio 0)
  have hP : IsPreconnected P :=
    (hcv.inter ((convex_Ioi (0 : ℝ)).linear_preimage ell.toLinearMap)).isPreconnected.image
      H.symm (H.continuousOn_symm.mono inter_subset_left)
  have hN : IsPreconnected N :=
    (hcv.inter ((convex_Iio (0 : ℝ)).linear_preimage ell.toLinearMap)).isPreconnected.image
      H.symm (H.continuousOn_symm.mono inter_subset_left)
  have hPmem (x : X) (hx : x ∈ H.source) : x ∈ P ↔ 0 < ell (H x) := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [H.right_inv hy.1]
      exact hy.2
    · intro ht
      exact ⟨H x, ⟨H.map_source hx, ht⟩, H.left_inv hx⟩
  have hNmem (x : X) (hx : x ∈ H.source) : x ∈ N ↔ ell (H x) < 0 := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [H.right_inv hy.1]
      exact hy.2
    · intro ht
      exact ⟨H x, ⟨H.map_source hx, ht⟩, H.left_inv hx⟩
  have hcover : H.source \ frontier D = P ∪ N := by
    ext x
    constructor
    · rintro ⟨hx, hn⟩
      have hne : ell (H x) ≠ 0 := fun h => hn ((hfront x hx).mpr h)
      rcases lt_or_gt_of_ne hne with ht | ht
      · exact Or.inr ((hNmem x hx).mpr ht)
      · exact Or.inl ((hPmem x hx).mpr ht)
    · rintro (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
      · refine ⟨H.map_target hy.1, ?_⟩
        intro hf
        have heq := (hfront (H.symm y) (H.map_target hy.1)).mp hf
        rw [H.right_inv hy.1] at heq
        exact (ne_of_gt hy.2) heq
      · refine ⟨H.map_target hy.1, ?_⟩
        intro hf
        have heq := (hfront (H.symm y) (H.map_target hy.1)).mp hf
        rw [H.right_inv hy.1] at heq
        exact (ne_of_lt hy.2) heq
  have hzero (x : X) (hx : x ∈ H.source) (ht : ell (H x) = 0) : x ∈ D :=
    hD.frontier_subset ((hfront x hx).mpr ht)
  rcases hD.local_complementary_sides hreg hp H.open_source hpH hP hN hcover with h | h
  · left
    intro x hx
    constructor
    · intro hxD
      by_contra hn
      exact h.2 ((hNmem x hx).mpr (lt_of_not_ge hn)) hxD
    · intro ht
      rcases eq_or_lt_of_le ht with heq | hlt
      · exact hzero x hx heq.symm
      · exact interior_subset (h.1 ((hPmem x hx).mpr hlt))
  · right
    intro x hx
    constructor
    · intro hxD
      by_contra hn
      exact h.2 ((hPmem x hx).mpr (lt_of_not_ge hn)) hxD
    · intro ht
      rcases eq_or_lt_of_le ht with heq | hlt
      · exact hzero x hx heq
      · exact interior_subset (h.1 ((hNmem x hx).mpr hlt))

end PoincareConjecture.M76
