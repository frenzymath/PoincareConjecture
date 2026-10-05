/-
Copyright (c) 2026 The PoincareLib contributors.
-/
import Mathlib.Topology.Connected.Basic

/-!
# Complementary components incident to a boundary point

A neighborhood covered off the boundary by two preconnected sides can meet
at most two global complementary components at its center. If both sides
approach that center, their global components give the exact incidence list.
The two listed components may coincide.
-/

set_option autoImplicit false

open Set
open scoped Topology

namespace Poincare.Topology

variable {X : Type*} [TopologicalSpace X]

/-- A preconnected set avoiding a frontier and meeting the interior stays
entirely in that interior. -/
theorem preconnected_subset_interior_of_disjoint_frontier
    {A D : Set X} (hA : IsPreconnected A) (hfront : Disjoint A (frontier D))
    (hmeet : (A ∩ interior D).Nonempty) : A ⊆ interior D := by
  have hcover : A ⊆ interior D ∪ interior Dᶜ := by
    rw [← compl_frontier_eq_union_interior]
    exact disjoint_left.mp hfront
  apply hA.subset_left_of_subset_union isOpen_interior isOpen_interior _ hcover hmeet
  exact disjoint_left.mpr fun x hx hx' => (interior_subset hx') (interior_subset hx)

/-- A boundary point approached by a preconnected subset of the complement
lies in the frontier of the component containing that subset. -/
theorem mem_frontier_connectedComponentIn_of_preconnected
    {K U : Set X} {p u : X} (hU : IsPreconnected U) (hUK : U ⊆ Kᶜ)
    (hu : u ∈ U) (hpK : p ∈ K) (hpU : p ∈ closure U) :
    p ∈ frontier (connectedComponentIn Kᶜ u) := by
  refine ⟨closure_mono (hU.subset_connectedComponentIn hu hUK) hpU, ?_⟩
  intro h
  exact connectedComponentIn_subset Kᶜ u (interior_subset h) hpK

/-- Two local preconnected sides account for every global complementary
component whose frontier contains the center of the neighborhood. -/
theorem connectedComponentIn_eq_or_eq_of_two_sided_neighborhood
    {K W U V : Set X} {p u v x : X} (hW : W ∈ 𝓝 p)
    (hpartition : W \ K = U ∪ V)
    (hU : IsPreconnected U) (hV : IsPreconnected V) (hu : u ∈ U) (hv : v ∈ V)
    (hp : p ∈ frontier (connectedComponentIn Kᶜ x)) :
    connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ u ∨
      connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ v := by
  have hUV : U ∪ V ⊆ Kᶜ := by
    rw [← hpartition]
    exact sdiff_subset_compl W K
  obtain ⟨z, hzW, hzC⟩ := mem_closure_iff.mp (frontier_subset_closure hp)
    (interior W) isOpen_interior (mem_interior_iff_mem_nhds.mpr hW)
  have hzUV : z ∈ U ∪ V := by
    rw [← hpartition]
    exact ⟨interior_subset hzW, connectedComponentIn_subset Kᶜ x hzC⟩
  rcases hzUV with hzU | hzV
  · exact Or.inl ((connectedComponentIn_eq hzC).trans (connectedComponentIn_eq
      (hU.subset_connectedComponentIn hu (subset_union_left.trans hUV) hzU)).symm)
  · exact Or.inr ((connectedComponentIn_eq hzC).trans (connectedComponentIn_eq
      (hV.subset_connectedComponentIn hv (subset_union_right.trans hUV) hzV)).symm)

/-- When both local sides approach a point of `K`, the global complementary
components incident to that point are exactly those containing the two sides.
This does not require the two global components to be distinct. -/
theorem mem_frontier_connectedComponentIn_iff_of_two_sided_neighborhood
    {K W U V : Set X} {p u v x : X} (hW : W ∈ 𝓝 p)
    (hpartition : W \ K = U ∪ V)
    (hU : IsPreconnected U) (hV : IsPreconnected V) (hu : u ∈ U) (hv : v ∈ V)
    (hpK : p ∈ K) (hpU : p ∈ closure U) (hpV : p ∈ closure V) :
    p ∈ frontier (connectedComponentIn Kᶜ x) ↔
      connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ u ∨
        connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ v := by
  constructor
  · exact connectedComponentIn_eq_or_eq_of_two_sided_neighborhood
      hW hpartition hU hV hu hv
  · have hUV : U ∪ V ⊆ Kᶜ := by
      rw [← hpartition]
      exact sdiff_subset_compl W K
    rintro (heq | heq)
    · rw [heq]
      exact mem_frontier_connectedComponentIn_of_preconnected
        hU (subset_union_left.trans hUV) hu hpK hpU
    · rw [heq]
      exact mem_frontier_connectedComponentIn_of_preconnected
        hV (subset_union_right.trans hUV) hv hpK hpV

end Poincare.Topology
