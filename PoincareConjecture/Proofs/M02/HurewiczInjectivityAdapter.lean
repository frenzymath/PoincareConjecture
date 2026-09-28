import PoincareConjecture.Proofs.M02.HurewiczRepresentatives
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

set_option autoImplicit false

open CategoryTheory Limits

universe w

namespace PoincareConjecture.Proofs.M02

theorem subsingleton_homotopyGroupPi_of_integral_hurewicz_injective_isZero
    (X : TopCat.{w}) (n : ℕ) (x : X)
    (hzero : IsZero ((TopCat.toSSet.obj X).homology
      (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)))
    (hinj : Function.Injective
      (homotopyGroupSingularHomologyMap
        (ModuleCat.of ℤ (ULift.{w} ℤ)) X n x)) :
    Subsingleton (HomotopyGroup.Pi (n + 1) X x) := by
  constructor
  intro a b
  apply hinj
  exact hzero.eq_of_tgt _ _

end PoincareConjecture.Proofs.M02
