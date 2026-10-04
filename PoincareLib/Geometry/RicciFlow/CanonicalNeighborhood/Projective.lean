import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.RoundCylinder

/-!
# The antipodal projective-plane model

Ported from Mapher `Definitions/Ch09/CanonicalNeighborhoods.lean` at
`49331b7d7ecad38f53e4300c3b35d6a84b2cc648`, with declaration bodies unchanged.
-/

set_option autoImplicit false

namespace PoincareMT

/-- The antipodal quotient model of the projective plane. -/
instance realProjectiveTwoSetoid : Setoid UnitTwoSphere where
  r x y := x = y ∨ x = -y
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro x; exact Or.inl rfl
    · intro x y h
      rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h]; simp)
    · intro x y z hxy hyz
      rcases hxy with hxy | hxy <;> rcases hyz with hyz | hyz
      · exact Or.inl (hxy.trans hyz)
      · exact Or.inr (by simpa [hxy] using hyz)
      · exact Or.inr (by simpa [hyz] using hxy)
      · exact Or.inl (by rw [hxy, hyz]; simp)

abbrev RealProjectiveTwo := Quotient realProjectiveTwoSetoid

end PoincareMT
