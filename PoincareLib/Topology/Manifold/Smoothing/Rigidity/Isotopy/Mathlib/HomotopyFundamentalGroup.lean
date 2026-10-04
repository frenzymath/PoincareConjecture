import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Isotopy.Mathlib.IdentityHomotopy
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-!
# The actual based map induced by a homotopy equivalence

The fundamental-groupoid equivalence retains the supplied forward
map. Fullness and faithfulness therefore apply to that exact based
homomorphism, with its literal image basepoint. See Waldhausen1968,
pp.60,77--79, Hamilton1976 p.65, and rigidity052, section1.
-/

set_option autoImplicit false

open CategoryTheory

namespace FundamentalGroup

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z]

/-- The original loop maps compose at their literal image
basepoints. See rigidity052, sections1--2. -/
theorem map_comp_apply (f : C(X, Y)) (g : C(Y, Z)) (x : X)
    (a : FundamentalGroup X x) :
    map (g.comp f) x a = map g (f x) (map f x a) := by
  obtain ⟨a, rfl⟩ := Path.Homotopic.Quotient.mk_surjective a
  rfl

/-- A homotopy equivalence makes its actual based forward map
bijective, without replacing the image basepoint. See052, section1. -/
theorem map_bijective_of_homotopyEquiv (h : ContinuousMap.HomotopyEquiv X Y) (x : X) :
    Function.Bijective (map h.toFun x) := by
  let e := FundamentalGroupoidFunctor.equivOfHomotopyEquiv h
  let : e.functor.Faithful := e.faithful_functor
  let : e.functor.Full := e.full_functor
  exact ⟨e.functor.map_injective, e.functor.map_surjective⟩

/-- Package the same actual homomorphism as a group isomorphism;
no independent abstract group comparison is chosen. See052, section1. -/
noncomputable def homotopyEquivMapMulEquiv
    (h : ContinuousMap.HomotopyEquiv X Y) (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (h.toFun x) :=
  MulEquiv.ofBijective (map h.toFun x) (map_bijective_of_homotopyEquiv h x)

/-- The constructed group isomorphism is the original loop map
on every class. See rigidity052, section1. -/
theorem homotopyEquivMapMulEquiv_apply
    (h : ContinuousMap.HomotopyEquiv X Y) (x : X) (a : FundamentalGroup X x) :
    homotopyEquivMapMulEquiv h x a = map h.toFun x a := rfl

end FundamentalGroup

namespace ContinuousMap.HomotopyRel

variable {X : Type*} [TopologicalSpace X] {f : C(X, X)} {S : Set X}

/-- The supplied relative identity homotopy gives bijectivity
of this same map at every original basepoint. See052, section1. -/
theorem fundamentalGroup_map_bijective
    (F : (ContinuousMap.id X).HomotopyRel f S) (x : X) :
    Function.Bijective (FundamentalGroup.map f x) :=
  FundamentalGroup.map_bijective_of_homotopyEquiv F.homotopyEquivOfId x

end ContinuousMap.HomotopyRel
