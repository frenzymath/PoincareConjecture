import PoincareConjecture.Proofs.M02.Topology.IntegralLocalHomology










set_option autoImplicit false

noncomputable section

open CategoryTheory

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable {X : Type u} [TopologicalSpace X]

def integralLocalRelativeHomologyAmbientIso
    [T1Space X] (x : X) (U : Set X) (hU : IsOpen U) (hx : x ∈ U) (n : Nat) :
    integralRelativeHomology ((Subtype.val : U → X) ⁻¹' ({x}ᶜ : Set X)) n ≅
      integralRelativeHomology ({x}ᶜ : Set X) n :=
  letI : IsIso (HomologicalComplex.homologyMap (integralLocalRelativeMap x U) n) :=
    integral_local_relative_excision x U hU hx n
  asIso (HomologicalComplex.homologyMap (integralLocalRelativeMap x U) n)

def integralLocalRelativeHomologyTransport
    [T1Space X] (x : X) (U V : Set X)
    (hU : IsOpen U) (hxU : x ∈ U) (hV : IsOpen V) (hxV : x ∈ V) (n : Nat) :
    integralRelativeHomology ((Subtype.val : U → X) ⁻¹' ({x}ᶜ : Set X)) n ≅
      integralRelativeHomology ((Subtype.val : V → X) ⁻¹' ({x}ᶜ : Set X)) n :=
  integralLocalRelativeHomologyAmbientIso x U hU hxU n ≪≫
    (integralLocalRelativeHomologyAmbientIso x V hV hxV n).symm

theorem integralLocalRelativeHomologyTransport_comp_ambient
    [T1Space X] (x : X) (U V : Set X)
    (hU : IsOpen U) (hxU : x ∈ U) (hV : IsOpen V) (hxV : x ∈ V) (n : Nat) :
    (integralLocalRelativeHomologyTransport x U V hU hxU hV hxV n).hom ≫
        HomologicalComplex.homologyMap (integralLocalRelativeMap x V) n =
      HomologicalComplex.homologyMap (integralLocalRelativeMap x U) n := by
  let : IsIso (HomologicalComplex.homologyMap (integralLocalRelativeMap x U) n) :=
    integral_local_relative_excision x U hU hxU n
  let : IsIso (HomologicalComplex.homologyMap (integralLocalRelativeMap x V) n) :=
    integral_local_relative_excision x V hV hxV n
  change (asIso (HomologicalComplex.homologyMap (integralLocalRelativeMap x U) n)).hom ≫
      ((asIso (HomologicalComplex.homologyMap (integralLocalRelativeMap x V) n)).inv ≫
        (asIso (HomologicalComplex.homologyMap (integralLocalRelativeMap x V) n)).hom) = _
  rw [(asIso (HomologicalComplex.homologyMap (integralLocalRelativeMap x V) n)).inv_hom_id,
    Category.comp_id]
  rfl

theorem integralLocalRelativeHomologyTransport_unique
    [T1Space X] (x : X) (U V : Set X)
    (hU : IsOpen U) (hxU : x ∈ U) (hV : IsOpen V) (hxV : x ∈ V) (n : Nat)
    (f : integralRelativeHomology ((Subtype.val : U → X) ⁻¹' ({x}ᶜ : Set X)) n ⟶
      integralRelativeHomology ((Subtype.val : V → X) ⁻¹' ({x}ᶜ : Set X)) n)
    (hf : f ≫ HomologicalComplex.homologyMap (integralLocalRelativeMap x V) n =
      HomologicalComplex.homologyMap (integralLocalRelativeMap x U) n) :
    f = (integralLocalRelativeHomologyTransport x U V hU hxU hV hxV n).hom := by
  let : IsIso (HomologicalComplex.homologyMap (integralLocalRelativeMap x V) n) :=
    integral_local_relative_excision x V hV hxV n
  apply (cancel_mono (HomologicalComplex.homologyMap (integralLocalRelativeMap x V) n)).mp
  rw [hf, integralLocalRelativeHomologyTransport_comp_ambient]

end PoincareConjecture.Proofs.M02.Topology
