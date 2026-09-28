import PoincareConjecture.Proofs.M83.Mathlib.SmallChainMap
import PoincareConjecture.Proofs.M02.Topology.IntegralOpenMayerVietoris
import PoincareConjecture.Proofs.M02.Topology.IntegralSupportMayerVietoris
import Mathlib.Algebra.Homology.HomologySequenceLemmas

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits HomologicalComplex Set

universe u

namespace PoincareConjecture.Proofs.M83

open PoincareConjecture.Proofs.M02.Topology

variable {X : Type u} [TopologicalSpace X]

def coverIntersectionMap (A B : Set X) (f : C(X, X))
    (hAB : MapsTo f A B) (hBA : MapsTo f B A) : C(↥(A ∩ B), ↥(A ∩ B)) :=
  ⟨fun x => ⟨f x, hBA x.property.2, hAB x.property.1⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem openCoverSwap_connecting
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = univ)
    (f : C(X, X)) (hAB : MapsTo f A B) (hBA : MapsTo f B A) (n : Nat) :
    homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) (n + 1) ≫
        integralOpenHomologyConnecting A B hA hB hcover n =
      -(integralOpenHomologyConnecting A B hA hB hcover n ≫
        homologyMap (integralChainsFunctor.map
          (TopCat.ofHom (coverIntersectionMap A B f hAB hBA))) n) := by
  let a : C(A, B) := ⟨fun x => ⟨f x, hAB x.property⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let b : C(B, A) := ⟨fun x => ⟨f x, hBA x.property⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let i := integralChainsFunctor.map (TopCat.ofHom (coverIntersectionMap A B f hAB hBA))
  let m : integralChains A ⊞ integralChains B ⟶ integralChains A ⊞ integralChains B :=
    biprod.desc (integralChainsFunctor.map (TopCat.ofHom a) ≫ biprod.inr)
      (integralChainsFunctor.map (TopCat.ofHom b) ≫ biprod.inl)
  have hf : ∀ t : Bool, MapsTo f (integralBinaryCover A B t)
      (integralBinaryCover A B (!t)) := by
    intro t
    cases t
    · exact hBA
    · exact hAB
  let c := integralSmallChainsMap (integralBinaryCover A B)
    (integralBinaryCover A B) Bool.not f hf
  have hiA : i ≫ integralNestedChains (inter_subset_left : A ∩ B ⊆ A) =
      integralNestedChains (inter_subset_right : A ∩ B ⊆ B) ≫
        integralChainsFunctor.map (TopCat.ofHom b) := by
    dsimp only [i, integralNestedChains]
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    rfl
  have hiB : i ≫ integralNestedChains (inter_subset_right : A ∩ B ⊆ B) =
      integralNestedChains (inter_subset_left : A ∩ B ⊆ A) ≫
        integralChainsFunctor.map (TopCat.ofHom a) := by
    dsimp only [i, integralNestedChains]
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    rfl
  have hdiff : (-i) ≫ integralOpenDifference A B = integralOpenDifference A B ≫ m := by
    apply biprod.hom_ext
    · simp [m, integralOpenDifference, Preadditive.neg_comp, hiA]
    · simp [m, integralOpenDifference, Preadditive.neg_comp, hiB]
  have hsum : m ≫ integralOpenSum A B = integralOpenSum A B ≫ c := by
    let := integralSmallChainInclusion_mono (integralBinaryCover A B)
    apply (cancel_mono (integralSmallChainInclusion (integralBinaryCover A B))).mp
    rw [Category.assoc, integralOpenSum_inclusion, Category.assoc,
      integralSmallChainsMap_inclusion, ← Category.assoc, integralOpenSum_inclusion]
    apply biprod.hom_ext'
    · simp only [m, biprod.inl_desc_assoc, Category.assoc, biprod.inr_desc,
        integralSubspaceChains]
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
      rfl
    · simp only [m, biprod.inr_desc_assoc, Category.assoc, biprod.inl_desc,
        integralSubspaceChains]
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
      rfl
  let S := integralOpenChainSequence A B
  let hS := integralOpenChainSequence_shortExact A B
  let F : S ⟶ S := { τ₁ := -i, τ₂ := m, τ₃ := c, comm₁₂ := hdiff, comm₂₃ := hsum }
  have hn := HomologySequence.δ_naturality F hS hS (n + 1) n rfl
  change hS.δ (n + 1) n rfl ≫ homologyMap (-i) n =
    homologyMap c (n + 1) ≫ hS.δ (n + 1) n rfl at hn
  rw [homologyMap_neg, Preadditive.comp_neg] at hn
  let e := integralOpenHomologyIso A B hA hB hcover (n + 1)
  have hc : homologyMap c (n + 1) ≫ e.hom =
      e.hom ≫ homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) (n + 1) := by
    change homologyMap c (n + 1) ≫
        homologyMap (integralSmallChainInclusion (integralBinaryCover A B)) (n + 1) = _
    rw [← homologyMap_comp, integralSmallChainsMap_inclusion, homologyMap_comp]
    rfl
  apply (cancel_epi e.hom).mp
  change e.hom ≫ homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) (n + 1) ≫
      e.inv ≫ hS.δ (n + 1) n rfl =
    e.hom ≫ (-(e.inv ≫ hS.δ (n + 1) n rfl ≫ homologyMap i n))
  rw [← Category.assoc e.hom, ← hc]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Preadditive.comp_neg]
  exact hn.symm

theorem openCoverSwap_homology_neg
    (A B : Set X) [ContractibleSpace A] [ContractibleSpace B]
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = univ)
    (f : C(X, X)) (hAB : MapsTo f A B) (hBA : MapsTo f B A) (n : Nat)
    (hi : homologyMap (integralChainsFunctor.map
      (TopCat.ofHom (coverIntersectionMap A B f hAB hBA))) n = 𝟙 _) :
    homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) (n + 1) =
      -𝟙 (integralHomology X (n + 1)) := by
  have hAz := ModuleCat.isZero_iff_subsingleton.mp
    (integral_contractible_homology_isZero A (n + 1) (by omega))
  have hBz := ModuleCat.isZero_iff_subsingleton.mp
    (integral_contractible_homology_isZero B (n + 1) (by omega))
  have hz : IsZero ((integralChains A ⊞ integralChains B).homology (n + 1)) :=
    ModuleCat.isZero_iff_subsingleton.mpr ⟨fun a b =>
      integralHomologyBiprod_ext _ _ _ (hAz.elim _ _) (hBz.elim _ _)⟩
  let hS := integralOpenChainSequence_shortExact A B
  let : Mono (hS.δ (n + 1) n rfl) :=
    (hS.homology_exact₃ (n + 1) n rfl).mono_g (hz.eq_of_src _ _)
  let : Mono (integralOpenHomologyConnecting A B hA hB hcover n) := by
    dsimp only [integralOpenHomologyConnecting]
    infer_instance
  apply (cancel_mono (integralOpenHomologyConnecting A B hA hB hcover n)).mp
  rw [openCoverSwap_connecting A B hA hB hcover f hAB hBA n, hi,
    Category.comp_id, Preadditive.neg_comp, Category.id_comp]

end PoincareConjecture.Proofs.M83
