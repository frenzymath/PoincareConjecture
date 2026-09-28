import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.Even










set_option autoImplicit false

namespace AddEquiv




theorem even_apply_iff {A B : Type*} [AddMonoid A] [AddMonoid B]
    (e : A ≃+ B) (a : A) : Even (e a) ↔ Even a := by
  constructor
  · intro h
    simpa using h.map e.symm
  · exact fun h => h.map e

end AddEquiv
