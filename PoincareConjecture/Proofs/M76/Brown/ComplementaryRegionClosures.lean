import Mathlib.Topology.Closure

set_option autoImplicit false

open Set

namespace BrownCollar

variable {X : Type*} [TopologicalSpace X] {S U V : Set X}

theorem closure_region_eq_compl (hdis : Disjoint U V) (hunion : U ∪ V = Sᶜ)
    (hfront : frontier U = S) : closure U = Vᶜ := by
  rw [closure_eq_self_union_frontier, hfront]
  ext x
  constructor
  · rintro (hxU | hxS) hxV
    · exact Set.disjoint_left.mp hdis hxU hxV
    · exact (hunion.subset (Or.inr hxV)) hxS
  · intro hxV
    by_cases hxS : x ∈ S
    · exact Or.inr hxS
    · exact Or.inl ((hunion.symm.subset hxS).resolve_right hxV)

theorem interior_closure_region (hdis : Disjoint U V) (hunion : U ∪ V = Sᶜ)
    (hfrontU : frontier U = S) (hfrontV : frontier V = S) : interior (closure U) = U := by
  have hUV : closure U = Vᶜ := closure_region_eq_compl hdis hunion hfrontU
  have hVU : closure V = Uᶜ :=
    closure_region_eq_compl hdis.symm ((union_comm V U).trans hunion) hfrontV
  rw [hUV, interior_compl, hVU, compl_compl]

theorem frontier_closure_region (hU : IsOpen U) (hdis : Disjoint U V)
    (hunion : U ∪ V = Sᶜ) (hfrontU : frontier U = S) (hfrontV : frontier V = S) :
    frontier (closure U) = S := by
  calc
    frontier (closure U) = closure U \ U := by
      rw [frontier, closure_closure, interior_closure_region hdis hunion hfrontU hfrontV]
    _ = frontier U := by rw [frontier, hU.interior_eq]
    _ = S := hfrontU

end BrownCollar
