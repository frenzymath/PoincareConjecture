import PoincareConjecture.Proofs.M02.Topology.IntegralMayerVietoris

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable {X : Type u} [TopologicalSpace X]

def integralNestedRelativePairSequence (A B : Set X) (h : A ⊆ B) :
    ShortComplex (ChainComplex (ModuleCat.{u} Int) Nat) :=
  ShortComplex.mk (integralPairInclusion A B) (integralRelativeRestriction h)
    (by
      apply (cancel_epi
        (integralRelativeProjection ((Subtype.val : B → X) ⁻¹' A))).mp
      rw [← Category.assoc, integralPairInclusion_projection, Category.assoc,
        integralRelativeRestriction_projection,
        cokernel.condition]
      simp)

theorem integralNestedRelativePairSequence_shortExact
    (A B : Set X) (h : A ⊆ B) :
    (integralNestedRelativePairSequence A B h).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro y hy
    obtain ⟨c, hc⟩ := integralProjection_surjective
      (integralSubspaceChains A) n y
    have hz : (integralRelativeProjection B).f n c = 0 := by
      have hp := congrArg (fun f => f.f n c)
        (integralRelativeRestriction_projection h)
      change (integralRelativeRestriction h).f n
          ((integralRelativeProjection A).f n c) =
        (integralRelativeProjection B).f n c at hp
      rw [hc] at hp
      exact hp.symm.trans (by
        change (integralRelativeRestriction h).f n y = 0 at hy
        exact hy)
    obtain ⟨b, hb⟩ := (integralProjection_eq_zero_iff
      (integralSubspaceChains B) n c).mp hz
    refine ⟨(integralRelativeProjection
      ((Subtype.val : B → X) ⁻¹' A)).f n b, ?_⟩
    · have hp := congrArg (fun f => f.f n b)
        (integralPairInclusion_projection A B)
      change (integralPairInclusion A B).f n
          ((integralRelativeProjection
            ((Subtype.val : B → X) ⁻¹' A)).f n b) = y
      change (integralPairInclusion A B).f n
          ((integralRelativeProjection
            ((Subtype.val : B → X) ⁻¹' A)).f n b) =
        (integralRelativeProjection A).f n ((integralSubspaceChains B).f n b) at hp
      rw [hp, hb]
      exact hc
  · apply (ModuleCat.mono_iff_injective _).mpr
    exact integralPairInclusion_injective A B n
  · apply (ModuleCat.epi_iff_surjective _).mpr
    intro y
    obtain ⟨c, hc⟩ := integralProjection_surjective
      (integralSubspaceChains B) n y
    refine ⟨(integralRelativeProjection A).f n c, ?_⟩
    have hp := congrArg (fun f => f.f n c)
      (integralRelativeRestriction_projection h)
    change (integralRelativeRestriction h).f n
        ((integralRelativeProjection A).f n c) =
      (integralRelativeProjection B).f n c at hp
    exact hp.trans hc

def integralUnionMemberHomeomorph (A B : Set X) :
    B ≃ₜ ((Subtype.val : ↥(A ∪ B) → X) ⁻¹' B) where
  toFun b := ⟨⟨b.val, Or.inr b.property⟩, b.property⟩
  invFun b := ⟨b.val.val, b.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

def integralUnionIntersectionHomeomorph (A B : Set X) :
    ((Subtype.val : B → X) ⁻¹' A) ≃ₜ
      ((Subtype.val : ((Subtype.val : ↥(A ∪ B) → X) ⁻¹' B) → ↥(A ∪ B)) ⁻¹'
        ((Subtype.val : ↥(A ∪ B) → X) ⁻¹' A)) where
  toFun a := ⟨integralUnionMemberHomeomorph A B a.val, a.property⟩
  invFun a := ⟨(integralUnionMemberHomeomorph A B).symm a.val, a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := ((integralUnionMemberHomeomorph A B).continuous.comp
    continuous_subtype_val).subtype_mk _
  continuous_invFun := ((integralUnionMemberHomeomorph A B).symm.continuous.comp
    continuous_subtype_val).subtype_mk _

def integralUnionExcisionSourceIso (A B : Set X) :
    integralRelativeChains ((Subtype.val : B → X) ⁻¹' A) ≅
      integralRelativeChains
        ((Subtype.val : ((Subtype.val : ↥(A ∪ B) → X) ⁻¹' B) → ↥(A ∪ B)) ⁻¹'
          ((Subtype.val : ↥(A ∪ B) → X) ⁻¹' A)) :=
  cokernel.mapIso _ _
    (integralChainsFunctor.mapIso
      (TopCat.isoOfHomeo (integralUnionIntersectionHomeomorph A B)))
    (integralChainsFunctor.mapIso
      (TopCat.isoOfHomeo (integralUnionMemberHomeomorph A B))) (by
      simp only [Functor.mapIso_hom, integralSubspaceChains, ← Functor.map_comp]
      rfl)

def integralUnionLeftComparison (A B : Set X) :
    integralRelativeChains ((Subtype.val : B → X) ⁻¹' A) ⟶
      integralRelativeChains ((Subtype.val : ↥(A ∪ B) → X) ⁻¹' A) :=
  integralRelativeMap
    (⟨fun b => ⟨b.val, Or.inr b.property⟩,
      continuous_subtype_val.subtype_mk _⟩ : C(B, ↥(A ∪ B)))
    (show Set.MapsTo _ ((Subtype.val : B → X) ⁻¹' A)
      ((Subtype.val : ↥(A ∪ B) → X) ⁻¹' A) from fun _ hx => hx)

@[reassoc (attr := simp)]
theorem integralUnionLeftComparison_projection (A B : Set X) :
    integralRelativeProjection ((Subtype.val : B → X) ⁻¹' A) ≫
      integralUnionLeftComparison A B =
        integralNestedChains (Set.subset_union_right : B ⊆ A ∪ B) ≫
          integralRelativeProjection ((Subtype.val : ↥(A ∪ B) → X) ⁻¹' A) := by
  exact integralRelativeMap_projection _ _

theorem integralUnionLeftComparison_toRelative (A B : Set X) :
    integralUnionLeftComparison A B ≫ integralPairInclusion A (A ∪ B) =
      integralPairInclusion A B := by
  apply (cancel_epi (integralRelativeProjection ((Subtype.val : B → X) ⁻¹' A))).mp
  rw [← Category.assoc, integralUnionLeftComparison_projection,
    Category.assoc, integralPairInclusion_projection,
    ← Category.assoc, integralNestedChains_subspaceChains,
    integralPairInclusion_projection]

theorem integralUnionLeftComparison_homology_isIso
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (n : Nat) :
    IsIso (HomologicalComplex.homologyMap (integralUnionLeftComparison A B) n) := by
  let UA : Set ↥(A ∪ B) := (Subtype.val : ↥(A ∪ B) → X) ⁻¹' A
  let UB : Set ↥(A ∪ B) := (Subtype.val : ↥(A ∪ B) → X) ⁻¹' B
  let e := integralPairInclusion UA UB
  have hcover : UA ∪ UB = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro x
    exact x.property
  let : IsIso (HomologicalComplex.homologyMap e n) :=
    integral_open_cover_excision UA UB (hA.preimage continuous_subtype_val)
      (hB.preimage continuous_subtype_val) hcover n
  have hfactor : (integralUnionExcisionSourceIso A B).hom ≫ e =
      integralUnionLeftComparison A B := by
    apply (cancel_epi
      (integralRelativeProjection ((Subtype.val : B → X) ⁻¹' A))).mp
    simp only [integralUnionExcisionSourceIso, cokernel.mapIso_hom, cokernel.map,
      cokernel.π_desc_assoc, Functor.mapIso_hom]
    dsimp only [e, UA, UB]
    rw [Category.assoc, integralPairInclusion_projection,
      integralUnionLeftComparison_projection, ← Category.assoc]
    dsimp only [integralSubspaceChains]
    rw [← integralChainsFunctor.map_comp]
    rfl
  rw [← hfactor, HomologicalComplex.homologyMap_comp]
  infer_instance

def integralSumComparisonDiagram (A B : Set X) :
    ShortComplex.cokernelSequence (integralPairInclusion A B) ⟶
      integralNestedRelativePairSequence A (A ∪ B) Set.subset_union_left where
  τ₁ := integralUnionLeftComparison A B
  τ₂ := 𝟙 _
  τ₃ := integralSumComparison A B
  comm₁₂ := by
    change integralUnionLeftComparison A B ≫ integralPairInclusion A (A ∪ B) =
      integralPairInclusion A B ≫ 𝟙 _
    rw [Category.comp_id, integralUnionLeftComparison_toRelative]
  comm₂₃ := by
    change 𝟙 _ ≫ integralRelativeRestriction Set.subset_union_left =
      integralSumProjection A B ≫ integralSumComparison A B
    rw [Category.id_comp, integralSumProjection_comparison]

theorem integralSumComparison_quasiIso
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) :
    QuasiIso (integralSumComparison A B) := by
  have hS : (ShortComplex.cokernelSequence (integralPairInclusion A B)).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact _
      mono_f := integralPairInclusion_mono A B }
  have hleft : QuasiIso (integralUnionLeftComparison A B) := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact integralUnionLeftComparison_homology_isIso A B hA hB n
  have hid : QuasiIso (𝟙 (integralRelativeChains A)) := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    infer_instance
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃
    (integralSumComparisonDiagram A B) hS
    (integralNestedRelativePairSequence_shortExact A (A ∪ B) Set.subset_union_left)
    hleft hid

theorem integralSumComparison_homology_isIso
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (n : Nat) :
    IsIso (HomologicalComplex.homologyMap (integralSumComparison A B) n) := by
  let := integralSumComparison_quasiIso A B hA hB
  infer_instance

end PoincareConjecture.Proofs.M02.Topology
