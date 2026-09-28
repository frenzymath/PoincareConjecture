import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.MayerVietoris.IntegralOpenUnionMayerVietoris

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex TopologicalSpace Set

universe u

namespace Poincare.Topology

variable {X : Type u} [TopologicalSpace X]

theorem integralOpenUnionHomologySum_epi_of_connecting_zero
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (n : Nat)
    (hzero : ∀ y : integralHomology (integralOpenUnion U V) (n + 1),
      integralOpenUnionHomologyConnectingToIntersection U V hU hV n y = 0) :
    Epi (integralOpenUnionHomologySum U V (n + 1)) := by
  have hconn : integralOpenUnionHomologyConnectingToIntersection U V hU hV n = 0 := by
    ext y
    exact hzero y
  exact (integralOpenUnionHomologyMayerVietoris_exact_union U V hU hV n).epi_f hconn

theorem integralOpenUnionHomologySum_zero_epi
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) :
    Epi (integralOpenUnionHomologySum U V 0) := by
  let A := integralOpenUnionLeft U V
  let B := integralOpenUnionRight U V
  let S := integralOpenChainSequence A B
  let hS := integralOpenChainSequence_shortExact A B
  let : Epi ((integralOpenSum A B).f 0) :=
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS 0).epi_g
  let : Epi (HomologicalComplex.homologyMap (integralOpenSum A B) 0) :=
    HomologicalComplex.epi_homologyMap_of_epi_of_not_rel
      (integralOpenSum A B) 0 (by
        intro j hj
        simp [ComplexShape.down] at hj)
  let : Epi (HomologicalComplex.homologyMap (integralOpenSum A B) 0 ≫
      (integralOpenUnionHomologyIso U V hU hV 0).hom) := by
    infer_instance
  exact epi_of_epi_fac (integralOpenUnionHomologySum_transport U V hU hV 0)

end Poincare.Topology
