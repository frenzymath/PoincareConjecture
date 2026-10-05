import PoincareLib.Geometry.RicciFlow.Extinction.Width.Contradiction.Statement

/-!
# M70 finite-piece contradiction proof entry

This checked logical adapter applies the supplied M69 width bound and M67
nonnegativity at the supplied profile-negative time. It introduces no
admission. Constructing that time and a width path from the global flow
remains M71's task; earlier contracts remain read-only.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- The supplied finite-piece width cannot be both nonnegative and bounded
above by a negative profile value. This is the final inequality contradiction
in Morgan--Tian's Theorem 18.1 proof, p. 432, not an additional analytic
extinction theorem. The path, width estimate and negative time are inputs. -/
theorem m70FiniteExtinctionContradiction : M70FiniteExtinctionStatement.{u} := by
  intro g₀ D W T P K C H B A q hM61 hM64 hM65 X L I HX C69 J
  refine ⟨⟨?_⟩⟩
  exact (not_lt_of_ge
    ((HX.width_nonnegative _).trans (C69.profile.width_bound J.B))) J.profile_negative

end PoincareMT
