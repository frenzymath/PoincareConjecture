import Mathlib.Topology.Closure



set_option autoImplicit false
open Set Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductEndDisks

theorem interior_closure_eq_of_frontier_outward_density
    {X : Type*} [TopologicalSpace X] {O : Set X} (hO : IsOpen O)
    (hout : frontier O ⊆ closure (closure O)ᶜ) : interior (closure O) = O := by
  apply Subset.antisymm
  · intro x hx
    by_contra hxO
    have hf : x ∈ frontier O := by
      rw [hO.frontier_eq]
      exact ⟨interior_subset hx, hxO⟩
    have hc := hout hf
    rw [closure_compl] at hc
    exact hc hx
  · exact hO.subset_interior_iff.mpr subset_closure

theorem frontier_closure_eq_of_frontier_outward_density
    {X : Type*} [TopologicalSpace X] {O : Set X} (hO : IsOpen O)
    (hout : frontier O ⊆ closure (closure O)ᶜ) : frontier (closure O) = frontier O := by
  rw [isClosed_closure.frontier_eq, hO.frontier_eq,
    interior_closure_eq_of_frontier_outward_density hO hout]

theorem closure_compl_closure_eq_of_frontier_outward_density
    {X : Type*} [TopologicalSpace X] {O : Set X} (hO : IsOpen O)
    (hout : frontier O ⊆ closure (closure O)ᶜ) : closure (closure O)ᶜ = Oᶜ := by
  rw [closure_compl, interior_closure_eq_of_frontier_outward_density hO hout]

end PoincareConjecture.M76.Dehn.Annuli.ProductEndDisks
