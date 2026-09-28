import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.LinearTorus.IntegerMatrix

set_option autoImplicit false

namespace PoincareConjecture.M76.LinearTorus

def affineIntegerMatrixMap (p : ℝ) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (c : AddCircle p × AddCircle p) :
    C(AddCircle p × AddCircle p, AddCircle p × AddCircle p) :=
  ⟨fun x => c + integerMatrixMap p A x,
    continuous_const.add (integerMatrixMap p A).continuous⟩

@[simp] theorem affineIntegerMatrixMap_apply (p : ℝ)
    (A : Matrix (Fin 2) (Fin 2) ℤ) (c x : AddCircle p × AddCircle p) :
    affineIntegerMatrixMap p A c x = c + integerMatrixMap p A x := rfl

@[simp] theorem affineIntegerMatrixMap_zero (p : ℝ)
    (A : Matrix (Fin 2) (Fin 2) ℤ) (c : AddCircle p × AddCircle p) :
    affineIntegerMatrixMap p A c 0 = c := by simp

end PoincareConjecture.M76.LinearTorus
