import Mathlib.Data.Set.Lattice










set_option autoImplicit false

namespace Set




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
