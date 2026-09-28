import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.IdentityHomotopy
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

set_option autoImplicit false

open CategoryTheory

namespace FundamentalGroup

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z]

theorem map_comp_apply (f : C(X, Y)) (g : C(Y, Z)) (x : X)
    (a : FundamentalGroup X x) :
    map (g.comp f) x a = map g (f x) (map f x a) := by
  obtain ⟨a, rfl⟩ := Path.Homotopic.Quotient.mk_surjective a
  rfl

theorem map_bijective_of_homotopyEquiv (h : ContinuousMap.HomotopyEquiv X Y) (x : X) :
    Function.Bijective (map h.toFun x) := by
  let e := FundamentalGroupoidFunctor.equivOfHomotopyEquiv h
  let : e.functor.Faithful := e.faithful_functor
  let : e.functor.Full := e.full_functor
  exact ⟨e.functor.map_injective, e.functor.map_surjective⟩

noncomputable def homotopyEquivMapMulEquiv
    (h : ContinuousMap.HomotopyEquiv X Y) (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (h.toFun x) :=
  MulEquiv.ofBijective (map h.toFun x) (map_bijective_of_homotopyEquiv h x)

theorem homotopyEquivMapMulEquiv_apply
    (h : ContinuousMap.HomotopyEquiv X Y) (x : X) (a : FundamentalGroup X x) :
    homotopyEquivMapMulEquiv h x a = map h.toFun x a := rfl

end FundamentalGroup

namespace ContinuousMap.HomotopyRel

variable {X : Type*} [TopologicalSpace X] {f : C(X, X)} {S : Set X}

theorem fundamentalGroup_map_bijective
    (F : (ContinuousMap.id X).HomotopyRel f S) (x : X) :
    Function.Bijective (FundamentalGroup.map f x) :=
  FundamentalGroup.map_bijective_of_homotopyEquiv F.homotopyEquivOfId x

end ContinuousMap.HomotopyRel
