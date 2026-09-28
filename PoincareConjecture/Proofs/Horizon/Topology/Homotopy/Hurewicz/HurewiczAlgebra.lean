import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Hurewicz.HurewiczRepresentatives
import Mathlib.Algebra.Group.Equiv.TypeTags








set_option autoImplicit false

open CategoryTheory

universe w

namespace Poincare.Topology




theorem exists_homotopyGroupPi_mulEquiv_of_integral_hurewicz_bijective
    (X : TopCat.{w}) (n : ℕ) (x : X)
    (e : (ModuleCat.of ℤ (ULift.{w} ℤ) ⟶
      (TopCat.toSSet.obj X).homology (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)) ≃+ ℤ)
    (hbij : Function.Bijective
      (homotopyGroupSingularHomologyMap (ModuleCat.of ℤ (ULift.{w} ℤ)) X n x)) :
    Nonempty (HomotopyGroup.Pi (n + 1) X x ≃* Multiplicative ℤ) := by
  classical
  let R := ModuleCat.of ℤ (ULift.{w} ℤ)
  let F := homotopyGroupSingularHomologyHom R X n x
  have hF : Function.Bijective F := by
    constructor
    · intro a b hab
      apply hbij.1
      exact congrArg Multiplicative.toAdd hab
    · intro y
      obtain ⟨z, hz⟩ := hbij.2 (Multiplicative.toAdd y)
      refine ⟨z, ?_⟩
      apply Multiplicative.ext
      exact hz
  exact ⟨(MulEquiv.ofBijective F hF).trans (AddEquiv.toMultiplicative e)⟩

end Poincare.Topology
