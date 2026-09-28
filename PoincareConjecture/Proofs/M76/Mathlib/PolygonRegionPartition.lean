import PoincareConjecture.Proofs.M76.Mathlib.PolygonRegionIndex
import PoincareConjecture.Proofs.M76.Mathlib.PolygonRegionNesting

set_option autoImplicit false

open Set

namespace Polygon

theorem region_partition_of_index_sum {n m k : ℕ}
    (P : Polygon (ℝ × ℝ) (n + 3)) (Q : Polygon (ℝ × ℝ) (m + 3))
    (R : Polygon (ℝ × ℝ) (k + 3))
    (hP : P.HasSimplicialEdges) (hiP : Function.Injective P) (hvP : P.HasNonverticalEdges)
    (hQ : Q.HasSimplicialEdges) (hiQ : Function.Injective Q) (hvQ : Q.HasNonverticalEdges)
    (hR : R.HasSimplicialEdges) (hiR : Function.Injective R) (hvR : R.HasNonverticalEdges)
    (hQP : Q.boundary ℝ ⊆ closure P.inside) (hRP : R.boundary ℝ ⊆ closure P.inside)
    (hcover : P.boundary ℝ ⊆ Q.boundary ℝ ∪ R.boundary ℝ)
    (hsum : ∀ q, P.crossingIndex q = Q.crossingIndex q + R.crossingIndex q) :
    Disjoint Q.inside R.inside ∧ closure P.inside = closure Q.inside ∪ closure R.inside := by
  have hQinside := P.inside_subset_inside_of_boundary_subset Q hP hiP hQ hiQ hQP
  have hRinside := P.inside_subset_inside_of_boundary_subset R hP hiP hR hiR hRP
  constructor
  · refine Set.disjoint_left.mpr fun q hqQ hqR => ?_
    have hpvalue := P.crossingIndex_eq_one_or_neg_one_of_mem_inside hP hiP hvP (hQinside hqQ)
    have hqvalue := Q.crossingIndex_eq_one_or_neg_one_of_mem_inside hQ hiQ hvQ hqQ
    have hrvalue := R.crossingIndex_eq_one_or_neg_one_of_mem_inside hR hiR hvR hqR
    have heq := hsum q
    omega
  · apply Subset.antisymm
    · intro q hq
      by_cases hqQ : q ∈ Q.boundary ℝ
      · left
        exact frontier_subset_closure (by rwa [Q.frontier_inside hQ hiQ])
      by_cases hqR : q ∈ R.boundary ℝ
      · right
        exact frontier_subset_closure (by rwa [R.frontier_inside hR hiR])
      have hqP : q ∉ P.boundary ℝ := fun h => (hcover h).elim hqQ hqR
      have hqinside : q ∈ P.inside := by
        rw [closure_eq_self_union_frontier, P.frontier_inside hP hiP] at hq
        exact hq.resolve_right hqP
      have hpne := (P.mem_inside_iff_crossingIndex_ne_zero hP hiP hvP hqP).mp hqinside
      by_cases hqi : q ∈ Q.inside
      · exact Or.inl (subset_closure hqi)
      · right
        apply subset_closure
        apply (R.mem_inside_iff_crossingIndex_ne_zero hR hiR hvR hqR).mpr
        have hqzero : Q.crossingIndex q = 0 := by
          by_contra hn
          exact hqi ((Q.mem_inside_iff_crossingIndex_ne_zero hQ hiQ hvQ hqQ).mpr hn)
        have heq := hsum q
        omega
    · exact union_subset (closure_mono hQinside) (closure_mono hRinside)

end Polygon
