import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSupportRangeMap
import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSupportCap
import PoincareConjecture.Proofs.M02.Topology.IntegralSupportEmbeddingHomologyIso

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex TopologicalSpace Set

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable {I W : Type u} [TopologicalSpace I] [TopologicalSpace W]

def integralRangeSupportMap (f : C(I, W)) (R : Set W) :
    integralRelativeChains (f ⁻¹' Rᶜ) ⟶ integralSupportChains R :=
  integralRelativeMap f (fun _ hx => hx)

theorem integralRangeSupportMap_projection (f : C(I, W)) (R : Set W) :
    integralRelativeProjection (f ⁻¹' Rᶜ) ≫ integralRangeSupportMap f R =
      integralChainsFunctor.map (TopCat.ofHom f) ≫ integralRelativeProjection Rᶜ :=
  integralRelativeMap_projection f _

theorem integralRangeSupportMap_factor
    (f : C(I, W)) (hf : Function.Injective f)
    (R : Set W) (hR : R ⊆ range f) :
    integralSupportEmbeddingChains f hf (f ⁻¹' R) ≫
      integralSupportRestriction (image_preimage_eq_of_subset hR).symm.le =
      integralRangeSupportMap f R := by
  apply (cancel_epi (integralRelativeProjection (f ⁻¹' R)ᶜ)).mp
  rw [← Category.assoc, integralSupportEmbeddingChains_projection, Category.assoc,
    integralSupportRestriction_projection]
  exact (integralRangeSupportMap_projection f R).symm

theorem integralSupportRestriction_eq_iso {K L : Set W} (h : K = L) :
    integralSupportRestriction h.le =
      (integralRelativeSetIso (congrArg (fun S : Set W => Sᶜ) h).symm).hom := by
  apply (cancel_epi (integralRelativeProjection Lᶜ)).mp
  rw [integralSupportRestriction_projection, integralRelativeSetIso_projection]

theorem integralRangeSupportMap_homology_isIso [T2Space W]
    (f : C(I, W)) (hf : _root_.Topology.IsOpenEmbedding f)
    (R : Compacts W) (hR : (R : Set W) ⊆ range f) (q : Nat) :
    IsIso (homologyMap (integralRangeSupportMap f (R : Set W)) q) := by
  have hE : IsIso (homologyMap
      (integralSupportEmbeddingChains f hf.injective (f ⁻¹' (R : Set W))) q) :=
    integralSupportEmbeddingChains_homology_isIso f hf
      (integralCompactSupportRangePreimage f hf R hR) q
  let := hE
  have hF : IsIso (homologyMap (integralSupportRestriction
      (image_preimage_eq_of_subset hR).symm.le) q) := by
    rw [integralSupportRestriction_eq_iso (image_preimage_eq_of_subset hR).symm]
    change IsIso ((homologyFunctor (ModuleCat.{u} Int) (ComplexShape.down Nat) q).map
      (integralRelativeSetIso _).hom)
    infer_instance
  let := hF
  rw [← integralRangeSupportMap_factor f hf.injective (R : Set W) hR,
    homologyMap_comp]
  infer_instance

theorem integralCompactSupportCohomologyRangeMap_pullback_class [T2Space W]
    (f : C(I, W)) (hf : _root_.Topology.IsOpenEmbedding f)
    (R : Compacts W) (hR : (R : Set W) ⊆ range f) (q : Nat) :
    integralCompactSupportCohomologyRangeMap f hf R hR q =
      homologyMap (integralDualMap (integralRangeSupportMap f (R : Set W))) q ≫
        integralCompactSupportCohomologyClass
          (integralCompactSupportRangePreimage f hf R hR) q := by
  have he : integralSupportEmbeddingChains f hf.injective
      (integralCompactSupportRangePreimage f hf R hR : Set I) ≫
      integralSupportRestriction
        (integralCompactSupportRangePreimage_image_eq f hf R hR).symm.le =
      integralRangeSupportMap f (R : Set W) :=
    integralRangeSupportMap_factor f hf.injective (R : Set W) hR
  have hH := congrArg (fun g => homologyMap (integralDualMap g) q) he
  rw [integralDualMap_comp, homologyMap_comp] at hH
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun g => g ≫ integralCompactSupportCohomologyClass
      (integralCompactSupportRangePreimage f hf R hR) q) hH)

variable [T2Space I] [T2Space W] [RegularSpace I] [RegularSpace W]

variable (hDI : ∀ L : Set I, IsCompact L → IntegralSupportDetected L 3)
  (hDW : ∀ L : Set W, IsCompact L → IntegralSupportDetected L 3)
  (omegaI : ∀ x : I, integralSupportHomology ({x} : Set I) 3)
  (omegaW : ∀ x : W, integralSupportHomology ({x} : Set W) 3)
  (hlocalI : ∀ x : I, ∃ U : Set I, IsOpen U ∧ x ∈ U ∧
    ∃ b : integralSupportHomology U 3,
      ∀ y : I, ∀ hy : y ∈ U,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) 3 b = omegaI y)
  (hlocalW : ∀ x : W, ∃ U : Set W, IsOpen U ∧ x ∈ U ∧
    ∃ b : integralSupportHomology U 3,
      ∀ y : W, ∀ hy : y ∈ U,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) 3 b = omegaW y)

theorem integralCompactSupportOrientation_rangeMap
    (f : C(I, W)) (hf : _root_.Topology.IsOpenEmbedding f)
    (horient : ∀ K : Compacts I,
      homologyMap (integralSupportEmbeddingChains f hf.injective (K : Set I)) 3
        (integralCompactSupportOrientation hDI omegaI K hlocalI) =
      integralCompactSupportOrientation hDW omegaW (K.map f f.continuous) hlocalW)
    (R : Compacts W) (hR : (R : Set W) ⊆ range f) :
    homologyMap (integralRangeSupportMap f (R : Set W)) 3
        (integralCompactSupportOrientation hDI omegaI
          (integralCompactSupportRangePreimage f hf R hR) hlocalI) =
      integralCompactSupportOrientation hDW omegaW R hlocalW := by
  rw [← integralRangeSupportMap_factor f hf.injective (R : Set W) hR,
    homologyMap_comp]
  change homologyMap (integralSupportRestriction
      (image_preimage_eq_of_subset hR).symm.le) 3
    (homologyMap (integralSupportEmbeddingChains f hf.injective (f ⁻¹' (R : Set W))) 3
      (integralCompactSupportOrientation hDI omegaI
        (integralCompactSupportRangePreimage f hf R hR) hlocalI)) = _
  have he := horient (integralCompactSupportRangePreimage f hf R hR)
  change homologyMap
      (integralSupportEmbeddingChains f hf.injective (f ⁻¹' (R : Set W))) 3 _ = _ at he
  rw [he]
  exact integralCompactSupportOrientation_restrict hDW omegaW hlocalW
    (show R ≤ (integralCompactSupportRangePreimage f hf R hR).map f f.continuous from
      (integralCompactSupportRangePreimage_image_eq f hf R hR).symm.le)

omit [RegularSpace W] in
theorem integralCompactSupportCapTwo_rangeMap
    (f : C(I, W)) (hf : _root_.Topology.IsOpenEmbedding f)
    (R : Compacts W) (hR : (R : Set W) ⊆ range f)
    (phi : integralSupportCohomology (R : Set W) 2) :
    integralCompactSupportCapTwo hDI omegaI hlocalI
        (integralCompactSupportCohomologyRangeMap f hf R hR 2 phi) =
      integralSupportCapHomologyTwo (f ⁻¹' (R : Set W)ᶜ)
        (integralCompactSupportOrientation hDI omegaI
          (integralCompactSupportRangePreimage f hf R hR) hlocalI)
        (homologyMap (integralDualMap (integralRangeSupportMap f (R : Set W))) 2 phi) := by
  rw [integralCompactSupportCohomologyRangeMap_pullback_class]
  exact congrArg (fun g => g
    (homologyMap (integralDualMap (integralRangeSupportMap f (R : Set W))) 2 phi))
      (integralCompactSupportCapTwo_class hDI omegaI hlocalI
        (integralCompactSupportRangePreimage f hf R hR))

omit [RegularSpace W] in
theorem integralCompactSupportCapThree_rangeMap
    (f : C(I, W)) (hf : _root_.Topology.IsOpenEmbedding f)
    (R : Compacts W) (hR : (R : Set W) ⊆ range f)
    (phi : integralSupportCohomology (R : Set W) 3) :
    integralCompactSupportCapThree hDI omegaI hlocalI
        (integralCompactSupportCohomologyRangeMap f hf R hR 3 phi) =
      integralSupportCapHomologyThree (f ⁻¹' (R : Set W)ᶜ)
        (integralCompactSupportOrientation hDI omegaI
          (integralCompactSupportRangePreimage f hf R hR) hlocalI)
        (homologyMap (integralDualMap (integralRangeSupportMap f (R : Set W))) 3 phi) := by
  rw [integralCompactSupportCohomologyRangeMap_pullback_class]
  exact congrArg (fun g => g
    (homologyMap (integralDualMap (integralRangeSupportMap f (R : Set W))) 3 phi))
      (integralCompactSupportCapThree_class hDI omegaI hlocalI
        (integralCompactSupportRangePreimage f hf R hR))

end PoincareConjecture.Proofs.M02.Topology
