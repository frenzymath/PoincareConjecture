import Mathlib.Topology.Closure

set_option autoImplicit false

open Set

variable {X : Type*} [TopologicalSpace X] {A U V : Set X}

theorem closure_eq_compl_of_complementary_regions
    (hcover : Aᶜ = U ∪ V) (hdis : Disjoint U V) (hfront : frontier U = A) :
    closure U = Vᶜ := by
  rw [closure_eq_self_union_frontier, hfront]
  apply Subset.antisymm
  · rintro x (hxU | hxA) hxV
    · exact Set.disjoint_left.mp hdis hxU hxV
    · have hx : x ∈ Aᶜ := hcover.symm ▸ (Or.inr hxV : x ∈ U ∪ V)
      exact hx hxA
  · intro x hxV
    by_cases hxA : x ∈ A
    · exact Or.inr hxA
    · have hx : x ∈ U ∪ V := hcover ▸ hxA
      exact Or.inl (hx.resolve_right hxV)

theorem interior_closure_eq_of_complementary_regions
    (hcover : Aᶜ = U ∪ V) (hdis : Disjoint U V)
    (hU : frontier U = A) (hV : frontier V = A) : interior (closure U) = U := by
  have hcover' : Aᶜ = V ∪ U := hcover.trans (union_comm _ _)
  rw [closure_eq_compl_of_complementary_regions hcover hdis hU, interior_compl,
    closure_eq_compl_of_complementary_regions hcover' hdis.symm hV, compl_compl]

theorem frontier_closure_eq_of_complementary_regions
    (hcover : Aᶜ = U ∪ V) (hdis : Disjoint U V)
    (hU : frontier U = A) (hV : frontier V = A) : frontier (closure U) = A := by
  rw [closure_eq_compl_of_complementary_regions hcover hdis hU, frontier_compl, hV]
