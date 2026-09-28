import Mathlib.Data.Set.Function










set_option autoImplicit false

open Set

namespace Function

variable {X : Type*}




theorem mem_set_iff_of_exceptional_fiber_fixed_compl (g : X → X)
    {A D : Set X} (hAD : A ⊆ D)
    (hfib : ∀ x y, g x = g y ↔ x = y ∨ (x ∈ A ∧ y ∈ A))
    (hfix : EqOn g id Dᶜ) : ∀ x, g x ∈ D ↔ x ∈ D := by
  classical
  intro x
  constructor
  · intro hgx
    by_contra hx
    have he : g x = x := hfix hx
    exact hx (he ▸ hgx)
  · intro hx
    by_contra hgx
    have he : g (g x) = g x := hfix hgx
    rcases (hfib x (g x)).mp he.symm with hxx | ⟨_, hA⟩
    · exact hgx (hxx ▸ hx)
    · exact hgx (hAD hA)

end Function
