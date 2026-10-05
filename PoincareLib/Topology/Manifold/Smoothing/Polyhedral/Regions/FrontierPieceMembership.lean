import Mathlib.Topology.Closure

/-!
# Frontier membership on a contained piece

When the part of a smaller frontier away from the larger frontier
lies inside the larger set, removing precisely that interior part
recovers the larger frontier on the smaller piece. This is the
boundary invariant for Erickson's polygon gluing, pp. 8--10;
see M76 derivation 118.
-/

set_option autoImplicit false

open Set

/-- On a contained piece, the outer frontier is the piece's
frontier minus its designated interior attachment part.
No closedness or regularity assumption is needed.
See M76 derivation 118. -/
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
