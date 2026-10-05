import Mathlib.Data.Set.Lattice

/-!
# Outer-boundary membership in an attached pair

On one ball, the other ball's outer boundary contributes only
points already in the first outer boundary, because the carriers
meet in the attachment disk and its boundary is shared. See
Alexander 1924, p. 7 and M76 derivation 129.
-/

set_option autoImplicit false

namespace Set

/-- On one carrier, the other boundary piece adds no points
outside the first boundary piece when their overlap is confined
to the shared attachment boundary. See M76 derivation 129. -/
theorem mem_union_iff_of_intersections {X : Type*} {s u b c d q : Set X}
    (hcu : c ⊆ u) (hqb : q ⊆ b) (hsu : s ∩ u = d) (hcd : c ∩ d = q)
    {x : X} (hx : x ∈ s) : x ∈ b ∪ c ↔ x ∈ b := by
  constructor
  · rintro (hxb | hxc)
    · exact hxb
    · have hxd : x ∈ d := hsu ▸ And.intro hx (hcu hxc)
      exact hqb (hcd ▸ And.intro hxc hxd)
  · exact Or.inl

end Set
