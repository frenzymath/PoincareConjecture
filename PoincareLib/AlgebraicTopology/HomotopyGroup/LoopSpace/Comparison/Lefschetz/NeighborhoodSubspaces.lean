import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Compatibility.ThreeManifoldTopology
import Mathlib.Algebra.Homology.QuasiIso

/-!
# Literal neighborhood subspaces in Mayer-Vietoris

Open neighborhoods inside one fixed ambient space can also be regarded as
subspaces of their union. These homeomorphisms only add or remove subtype
proofs, so every map to the ambient space remains the original inclusion.
Source: the open-cover comparison in Hatcher, Theorem 2.27, pp. 128-130.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex

universe u

namespace PoincareMT.Proofs.M59

open M02.Topology

variable {X : Type u} [TopologicalSpace X]

/-- An included subspace is homeomorphic to the same set viewed
inside its containing subspace. Source: Hatcher, Theorem 2.27. -/
def nestedSubsetHomeomorph (S T : Set X) (h : T ⊆ S) :
    T ≃ₜ (Subtype.val ⁻¹' T : Set S) where
  toFun x := ⟨⟨x.val, h x.property⟩, x.property⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- The identified intersection, viewed inside a containing subspace,
retains its actual points and the actual two membership proofs.
Source: Hatcher, Theorem 2.27, pp. 128-130. -/
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
/-- A literal homeomorphism induces its actual singular-chain
quasi-isomorphism. Source: Hatcher, homotopy invariance and Theorem 2.27. -/
theorem homeomorphSingularChainMap_quasiIso
    {Y : Type u} [TopologicalSpace Y] (e : X ≃ₜ Y) :
    QuasiIso (SSet.chainComplexMap (TopCat.toSSet.map
      (TopCat.ofHom (⟨e, e.continuous⟩ : C(X, Y)))) integralCoefficient.{u}) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  change IsIso (integralHomologyIsoOfHomotopyEquiv e.toHomotopyEquiv n).hom
  infer_instance

end PoincareMT.Proofs.M59
