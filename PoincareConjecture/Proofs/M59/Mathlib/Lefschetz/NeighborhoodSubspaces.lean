import PoincareConjecture.Proofs.M02.Topology.IntegralHomologyEquiv
import Mathlib.Algebra.Homology.QuasiIso

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex

universe u

namespace PoincareConjecture.Proofs.M59

open M02.Topology

variable {X : Type u} [TopologicalSpace X]

def nestedSubsetHomeomorph (S T : Set X) (h : T ⊆ S) :
    T ≃ₜ (Subtype.val ⁻¹' T : Set S) where
  toFun x := ⟨⟨x.val, h x.property⟩, x.property⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

def intersectionSubsetHomeomorph (S A B L : Set X) (hA : A ⊆ S)
    (hL : A ∩ B = L) :
    L ≃ₜ ↥((Subtype.val ⁻¹' A : Set S) ∩ (Subtype.val ⁻¹' B : Set S)) where
  toFun x := ⟨⟨x.val, hA (show x.val ∈ A ∩ B from hL.symm ▸ x.property).1⟩,
    show x.val ∈ A ∩ B from hL.symm ▸ x.property⟩
  invFun x := ⟨x.val.val,
    show x.val.val ∈ L from hL ▸ (show x.val.val ∈ A ∩ B from x.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

set_option backward.isDefEq.respectTransparency false in

theorem homeomorphSingularChainMap_quasiIso
    {Y : Type u} [TopologicalSpace Y] (e : X ≃ₜ Y) :
    QuasiIso (SSet.chainComplexMap (TopCat.toSSet.map
      (TopCat.ofHom (⟨e, e.continuous⟩ : C(X, Y)))) integralCoefficient.{u}) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  change IsIso (integralHomologyIsoOfHomotopyEquiv e.toHomotopyEquiv n).hom
  infer_instance

end PoincareConjecture.Proofs.M59
