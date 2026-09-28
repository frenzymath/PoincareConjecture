import PoincareConjecture.Statements.M70










set_option autoImplicit false

universe u

namespace PoincareConjecture





theorem m70FiniteExtinctionContradiction : M70FiniteExtinctionStatement.{u} := by
  intro g₀ D W T P K C H B A q hM61 hM64 hM65 X L I HX C69 J
  refine ⟨⟨?_⟩⟩
  exact (not_lt_of_ge
    ((HX.width_nonnegative _).trans (C69.profile.width_bound J.B))) J.profile_negative

end PoincareConjecture
