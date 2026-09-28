import PoincareConjecture.Proofs.M25.Topology3D.Services
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhoodNesting
import Mathlib.Tactic

set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

theorem saddle_planar_closedRegion_subset_of_boundary_subset
    (A B : BallNeighborhoodChart E2 E2)
    (hboundary : B.boundary ⊆ A.closedRegion) :
    B.closedRegion ⊆ A.closedRegion := by
  have hdim : 1 < Module.rank ℝ E2 := by
    rw [← Module.finrank_eq_rank]
    norm_num [E2]
  have houtside : IsPreconnected A.closedRegionᶜ := by
    simpa only [A.inside_union_boundary, compl_eq_univ_sdiff] using
      (A.outside_connected hdim).isPreconnected
  have hdis : Disjoint A.closedRegionᶜ B.boundary :=
    disjoint_left.mpr (fun _ hyA hyB => hyA (hboundary hyB))
  rcases B.preconnected_subset_inside_or_outside houtside hdis with hin | hout
  · have hbounded := A.closedRegion_compact.isBounded.union B.inside_bounded
    have hall : (univ : Set E2) ⊆ A.closedRegion ∪ B.inside := by
      intro y _
      by_cases hy : y ∈ A.closedRegion
      · exact Or.inl hy
      · exact Or.inr (hin hy)
    exact False.elim (NormedSpace.unbounded_univ ℝ E2 (hbounded.subset hall))
  · intro y hy
    by_contra hyA
    exact hout hyA hy

end PoincareConjecture.M25.Topology3D
