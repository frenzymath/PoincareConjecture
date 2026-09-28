import PoincareConjecture.Proofs.M02.Topology.IntegralChartSupport

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex
open PoincareConjecture.Proofs.M02.Topology

universe u

namespace PoincareConjecture.Proofs.M53

variable {X : Type u} [TopologicalSpace X]

theorem integral_interior_cover_excision_quasiIso
    (A U : Set X) (hU : IsOpen U) (hcover : interior A ∪ U = Set.univ) :
    QuasiIso (integralPairInclusion A U) := by
  let I := interior A
  let AU : Set U := (Subtype.val : U → X) ⁻¹' A
  let IU : Set U := (Subtype.val : U → X) ⁻¹' I
  let IA : Set A := (Subtype.val : A → X) ⁻¹' I
  let UA : Set A := (Subtype.val : A → X) ⁻¹' U
  let hIA : I ⊆ A := interior_subset
  let hIU : IU ⊆ AU := Set.preimage_mono hIA
  let f : C(AU, A) :=
    ⟨fun x => ⟨x.val.val, x.property⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  let q := integralRelativeMap f
    (A := (Subtype.val : AU → U) ⁻¹' IU) (B := IA) (fun _ hx => hx)
  have hq : integralRelativeProjection ((Subtype.val : AU → U) ⁻¹' IU) ≫ q =
      integralChainsFunctor.map (TopCat.ofHom f) ≫ integralRelativeProjection IA :=
    integralRelativeMap_projection _ _
  let T : integralNestedRelativePairSequence IU AU hIU ⟶
      integralNestedRelativePairSequence I A hIA :=
    { τ₁ := q
      τ₂ := integralPairInclusion I U
      τ₃ := integralPairInclusion A U
      comm₁₂ := by
        change q ≫ integralPairInclusion I A =
          integralPairInclusion IU AU ≫ integralPairInclusion I U
        apply (cancel_epi (integralRelativeProjection
          ((Subtype.val : AU → U) ⁻¹' IU))).mp
        rw [← Category.assoc, hq]
        simp only [Category.assoc, integralPairInclusion_projection_assoc]
        rw [integralPairInclusion_projection I A, integralPairInclusion_projection I U]
        change integralChainsFunctor.map (TopCat.ofHom f) ≫
            integralSubspaceChains A ≫ integralRelativeProjection I =
          integralSubspaceChains AU ≫ integralSubspaceChains U ≫
            integralRelativeProjection I
        simp only [integralSubspaceChains, ← Category.assoc, ← Functor.map_comp]
        rfl
      comm₂₃ := by
        change integralPairInclusion I U ≫ integralRelativeRestriction hIA =
          integralRelativeRestriction hIU ≫ integralPairInclusion A U
        apply (cancel_epi (integralRelativeProjection IU)).mp
        rw [← Category.assoc, integralPairInclusion_projection, Category.assoc,
          integralRelativeRestriction_projection, ← Category.assoc,
          integralRelativeRestriction_projection, integralPairInclusion_projection] }
  have hmiddle : QuasiIso T.τ₂ := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact integral_open_cover_excision I U isOpen_interior hU hcover n
  have hleft : QuasiIso T.τ₁ := by
    let e : AU ≃ₜ UA :=
      { toFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
        invFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
        left_inv _ := rfl
        right_inv _ := rfl
        continuous_toFun :=
          ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
        continuous_invFun :=
          ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _ }
    let E := integralRelativeHomeomorphIso e
      ((Subtype.val : AU → U) ⁻¹' IU) ((Subtype.val : UA → A) ⁻¹' IA) (fun _ => Iff.rfl)
    have hf : E.hom ≫ integralPairInclusion IA UA = q := by
      apply (cancel_epi (integralRelativeProjection
        ((Subtype.val : AU → U) ⁻¹' IU))).mp
      rw [← Category.assoc, integralRelativeHomeomorphIso_projection, Category.assoc,
        integralPairInclusion_projection, hq]
      change integralChainsFunctor.map (TopCat.ofHom (e : C(AU, UA))) ≫
        integralSubspaceChains UA ≫ integralRelativeProjection IA =
          integralChainsFunctor.map (TopCat.ofHom f) ≫ integralRelativeProjection IA
      rw [← Category.assoc, integralSubspaceChains, ← Functor.map_comp]
      rfl
    have hcoverA : IA ∪ UA = Set.univ := by
      apply Set.eq_univ_iff_forall.mpr
      intro a
      have ha : a.val ∈ I ∪ U := by rw [hcover]; exact Set.mem_univ _
      exact ha
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    change IsIso (homologyMap q n)
    let : IsIso (homologyMap (integralPairInclusion IA UA) n) :=
      integral_open_cover_excision IA UA
        (isOpen_interior.preimage continuous_subtype_val)
        (hU.preimage continuous_subtype_val) hcoverA n
    rw [← hf, homologyMap_comp]
    infer_instance
  exact HomologySequence.quasiIso_τ₃ T
    (integralNestedRelativePairSequence_shortExact IU AU hIU)
    (integralNestedRelativePairSequence_shortExact I A hIA) hleft hmiddle

theorem integral_interior_cover_excision
    (A U : Set X) (hU : IsOpen U) (hcover : interior A ∪ U = Set.univ) (n : Nat) :
    IsIso (homologyMap (integralPairInclusion A U) n) := by
  let := integral_interior_cover_excision_quasiIso A U hU hcover
  infer_instance

end PoincareConjecture.Proofs.M53
