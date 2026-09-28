import Mathlib.Topology.Closure

set_option autoImplicit false

open Set

theorem frontier_mem_iff_of_subset {X : Type*} [TopologicalSpace X]
    {s t d : Set X} (hts : t ⊆ s) (hfront : frontier t ⊆ frontier s ∪ d)
    (hd : d ⊆ interior s) {x : X} (hx : x ∈ t) :
    x ∈ frontier s ↔ x ∈ frontier t ∧ x ∉ d := by
  constructor
  · intro hxs
    exact ⟨⟨subset_closure hx, fun hxt => hxs.2 (interior_mono hts hxt)⟩,
      fun hxd => hxs.2 (hd hxd)⟩
  · rintro ⟨hxt, hxd⟩
    exact (hfront hxt).resolve_right hxd
