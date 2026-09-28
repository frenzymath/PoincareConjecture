import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Models.OriginalOrientedComponent
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.FundamentalGroup.TopologicalAdapters










set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
  {D : Set E} {S : Set X}


def originalComponentAmbientMap (g : E → X) (H : D ≃ₜ S)
    (hH : ∀ z : D, (H z : X) = g z) : C(D, X) where
  toFun z := g z
  continuous_toFun := (continuous_subtype_val.comp H.continuous).congr hH

@[simp] theorem originalComponentAmbientMap_apply
    (g : E → X) (H : D ≃ₜ S) (hH : ∀ z : D, (H z : X) = g z) (z : D) :
    originalComponentAmbientMap g H hH z = g z := rfl

theorem originalComponentAmbientMap_eq
    (g : E → X) (H : D ≃ₜ S) (hH : ∀ z : D, (H z : X) = g z) :
    originalComponentAmbientMap g H hH =
      (⟨Subtype.val, continuous_subtype_val⟩ : C(S, X)).comp (H : C(D, S)) := by
  ext z
  exact (hH z).symm

private theorem mapOfEq_congr {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    {f g : C(Y, Z)} (hfg : f = g) {y : Y} {z : Z}
    (hf : f y = z) (hg : g y = z) :
    FundamentalGroup.mapOfEq f hf = FundamentalGroup.mapOfEq g hg := by
  subst g
  rfl

private theorem mapOfEq_rfl {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) (y : Y) :
    FundamentalGroup.mapOfEq f (rfl : f y = f y) = FundamentalGroup.map f y := by
  ext p
  rw [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl]
  rfl



theorem originalComponentAmbientGroup_factorization
    (g : E → X) (H : D ≃ₜ S) (hH : ∀ z : D, (H z : X) = g z) (z : D) :
    FundamentalGroup.mapOfEq (originalComponentAmbientMap g H hH) (hH z).symm =
      (FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(S, X)) (H z)).comp
        (H.fundamentalGroupMulEquiv z).toMonoidHom := by
  rw [mapOfEq_congr (originalComponentAmbientMap_eq g H hH) (hH z).symm rfl,
    mapOfEq_rfl, FundamentalGroup.map_comp]
  rfl


theorem originalComponentAmbientGroup_injective
    (g : E → X) (H : D ≃ₜ S) (hH : ∀ z : D, (H z : X) = g z) (z : D)
    (hinj : Function.Injective
      (FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(S, X)) (H z))) :
    Function.Injective (FundamentalGroup.map (originalComponentAmbientMap g H hH) z) := by
  have hmap : Function.Injective (FundamentalGroup.map
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(S, X)).comp (H : C(D, S))) z) := by
    rw [FundamentalGroup.map_comp]
    exact hinj.comp (H.fundamentalGroupMulEquiv z).injective
  exact Eq.mpr (congrArg (fun f : C(D, X) ↦ Function.Injective (FundamentalGroup.map f z))
    (originalComponentAmbientMap_eq g H hH)) hmap



theorem originalComponentGroup_nontrivial
    (H : D ≃ₜ S) (z : D) (hnt : Nontrivial (FundamentalGroup S (H z))) :
    Nontrivial (FundamentalGroup D z) := by
  let := hnt
  exact (H.fundamentalGroupMulEquiv z).symm.injective.nontrivial



theorem originalComponentGroups_at_original_basepoint
    (g : E → X) (H : D ≃ₜ S) (hH : ∀ z : D, (H z : X) = g z)
    (x : S) (hnt : Nontrivial (FundamentalGroup S x))
    (hinj : Function.Injective
      (FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(S, X)) x)) :
    H (H.symm x) = x ∧ g (H.symm x) = (x : X) ∧
      Nontrivial (FundamentalGroup D (H.symm x)) ∧
      Function.Injective
        (FundamentalGroup.map (originalComponentAmbientMap g H hH) (H.symm x)) := by
  refine ⟨H.apply_symm_apply x, ?_, ?_, ?_⟩
  · exact (hH (H.symm x)).symm.trans (congrArg Subtype.val (H.apply_symm_apply x))
  · apply originalComponentGroup_nontrivial H (H.symm x)
    simpa only [H.apply_symm_apply] using hnt
  · apply originalComponentAmbientGroup_injective g H hH (H.symm x)
    exact Eq.mpr (congrArg (fun y : S ↦ Function.Injective
      (FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(S, X)) y))
      (H.apply_symm_apply x)) hinj



theorem originalComponent_basepoint_eq_coordinates
    (g : E → X) (H : D ≃ₜ S) (hH : ∀ z : D, (H z : X) = g z)
    (phi : X → E) (hinverse : ∀ z ∈ D, phi (g z) = z) (x : S) :
    (H.symm x : E) = phi (x : X) := by
  have hgx : g (H.symm x) = (x : X) :=
    (hH (H.symm x)).symm.trans (congrArg Subtype.val (H.apply_symm_apply x))
  exact ((hinverse (H.symm x) (H.symm x).property).symm.trans (congrArg phi hgx))

end PoincareConjecture.M76
