import PoincareConjecture.Proofs.M02.HomotopyHomologyIso
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects





set_option autoImplicit false

open CategoryTheory Limits

universe w v u

namespace PoincareConjecture.Proofs.M02

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  [CategoryWithHomology C]

noncomputable section

variable {X Y : TopCat.{w}}



theorem isZero_singularHomology_of_homotopyEquiv
    (R : C) (n : ℕ) (e : ContinuousMap.HomotopyEquiv X Y)
    (hY : IsZero ((TopCat.toSSet.obj Y).homology R n)) :
    IsZero ((TopCat.toSSet.obj X).homology R n) := by
  exact hY.of_iso (singularHomologyIso_of_homotopyEquiv R n e)

end

end PoincareConjecture.Proofs.M02
