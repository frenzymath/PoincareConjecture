import Mathlib.Topology.Homotopy.Equiv









set_option autoImplicit false

universe u

namespace ContinuousMap.HomotopyRel

variable {X : Type u} [TopologicalSpace X] {f : C(X, X)} {S : Set X}




def homotopyEquivOfId (F : (ContinuousMap.id X).HomotopyRel f S) :
    ContinuousMap.HomotopyEquiv X X where
  toFun := f
  invFun := ContinuousMap.id X
  left_inv := by
    simpa only [ContinuousMap.id_comp] using
      (show f.Homotopic (ContinuousMap.id X) from ⟨F.toHomotopy.symm⟩)
  right_inv := by
    simpa only [ContinuousMap.comp_id] using
      (show f.Homotopic (ContinuousMap.id X) from ⟨F.toHomotopy.symm⟩)



@[simp]
theorem homotopyEquivOfId_toFun (F : (ContinuousMap.id X).HomotopyRel f S) :
    F.homotopyEquivOfId.toFun = f := rfl



@[simp]
theorem homotopyEquivOfId_invFun (F : (ContinuousMap.id X).HomotopyRel f S) :
    F.homotopyEquivOfId.invFun = ContinuousMap.id X := rfl

end ContinuousMap.HomotopyRel
