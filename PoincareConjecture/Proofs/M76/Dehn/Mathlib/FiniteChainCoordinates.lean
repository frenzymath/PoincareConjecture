import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TriangleChainCoordinates
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.StdBasis









set_option autoImplicit false

namespace PreAbstractSimplicialComplex.ModTwoCochains

variable (κ : Type*) [Finite κ]



noncomputable def coordinateChainEquiv :
    (κ → ZMod 2) ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (κ → ZMod 2) := by
  classical
  exact (Pi.basisFun (ZMod 2) κ).toDualEquiv

open Classical in


theorem coordinateChainEquiv_single (f : κ → ZMod 2) (q : κ) :
    coordinateChainEquiv κ f (Pi.single q 1) = f q := by
  change (Pi.basisFun (ZMod 2) κ).toDual f (Pi.single q 1) = f q
  simpa only [Pi.basisFun_apply, Pi.basisFun_repr] using
    (Pi.basisFun (ZMod 2) κ).toDual_apply_left f q

open Classical in


theorem coordinateChainEquiv_symm_apply
    (c : Module.Dual (ZMod 2) (κ → ZMod 2)) (q : κ) :
    (coordinateChainEquiv κ).symm c q = c (Pi.single q 1) := by
  have h := coordinateChainEquiv_single κ ((coordinateChainEquiv κ).symm c) q
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

open Classical in


theorem chain_eq_of_single
    (c d : Module.Dual (ZMod 2) (κ → ZMod 2))
    (h : ∀ q : κ, c (Pi.single q 1) = d (Pi.single q 1)) : c = d := by
  apply (Pi.basisFun (ZMod 2) κ).ext
  intro q
  simpa only [Pi.basisFun_apply] using h q

end PreAbstractSimplicialComplex.ModTwoCochains
