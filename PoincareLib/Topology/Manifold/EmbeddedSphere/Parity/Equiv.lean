import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.Even

/-!
# Divisibility by two under additive equivalences

This elementary invariance expresses the orientation independence of parity
in local integral homology. See Hatcher, *Algebraic Topology*, p. 235, and
derivation 02 in `proof-work/tasks/M53/derivations/`, for the separation repair
used in Morgan--Tian Proposition 15.12 and Remark 15.13, printed p. 365.
-/

set_option autoImplicit false

namespace AddEquiv

/-- Additive equivalences preserve and reflect divisibility by two. This is
the algebraic form of the orientation-independent parity used by Hatcher,
Section 3.3, printed p. 235. -/
theorem even_apply_iff {A B : Type*} [AddMonoid A] [AddMonoid B]
    (e : A ≃+ B) (a : A) : Even (e a) ↔ Even a := by
  constructor
  · intro h
    simpa using h.map e.symm
  · exact fun h => h.map e

end AddEquiv
