import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false

open Set Bornology

namespace Poincare.Topology.Plane

theorem infinite_frontier_of_bounded_nonempty_interior
    {U : Set (EuclideanSpace ℝ (Fin 2))} (hbounded : IsBounded U)
    (hne : (interior U).Nonempty) : (frontier U).Infinite := by
  intro hfinite
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 2)) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    norm_num
  have hconn := hfinite.countable.isConnected_compl_of_one_lt_rank hrank
  have hout : (closure U)ᶜ.Nonempty := nonempty_compl.mpr fun heq =>
    NormedSpace.unbounded_univ ℝ (EuclideanSpace ℝ (Fin 2)) (heq ▸ hbounded.closure)
  have hdisjoint : Disjoint (interior U) (interior Uᶜ) :=
    disjoint_left.mpr fun x hx hx' => (interior_subset hx') (interior_subset hx)
  rcases hconn.isPreconnected.subset_or_subset isOpen_interior isOpen_interior hdisjoint
    (by rw [compl_frontier_eq_union_interior]) with hinside | houtside
  · obtain ⟨x, hx⟩ := hout
    have hxfront : x ∈ (frontier U)ᶜ := fun h => hx (frontier_subset_closure h)
    exact hx (subset_closure (interior_subset (hinside hxfront)))
  · obtain ⟨x, hx⟩ := hne
    have hxfront : x ∈ (frontier U)ᶜ := by
      rw [compl_frontier_eq_union_interior]
      exact Or.inl hx
    exact (interior_subset (houtside hxfront)) (interior_subset hx)

theorem infinite_frontier_of_isOpen
    {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsOpen U)
    (hbounded : IsBounded U) (hne : U.Nonempty) : (frontier U).Infinite :=
  infinite_frontier_of_bounded_nonempty_interior hbounded (hU.interior_eq.symm ▸ hne)

theorem exists_frontier_not_mem_finite
    {U : Set (EuclideanSpace ℝ (Fin 2))} (hbounded : IsBounded U)
    (hne : (interior U).Nonempty) {s : Set (EuclideanSpace ℝ (Fin 2))} (hs : s.Finite) :
    ∃ x ∈ frontier U, x ∉ s := by
  apply Set.not_subset.mp
  intro hsub
  exact infinite_frontier_of_bounded_nonempty_interior hbounded hne (hs.subset hsub)

end Poincare.Topology.Plane
