import PoincareConjecture.Proofs.M02.Topology.IntegralSupportCohomologyMV
import PoincareConjecture.Proofs.M02.Topology.IntegralCompactCohomology
import Mathlib.Algebra.Homology.HomologySequenceLemmas

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits HomologicalComplex Set

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable {X : Type u} [TopologicalSpace X]

def integralSupportIntermediateRestriction {K L K' L' : Set X}
    (hK : K ⊆ K') (hL : L ⊆ L') :
    integralSupportIntermediateSequence K' L' ⟶ integralSupportIntermediateSequence K L := by
  let S := integralSupportIntermediateSequence K L
  let S' := integralSupportIntermediateSequence K' L'
  let u := integralSupportRestriction (union_subset_union hK hL)
  let v := biprod.map (integralSupportRestriction hK) (integralSupportRestriction hL)
  have huv : u ≫ S.f = S'.f ≫ v := by
    apply biprod.hom_ext
    · simp only [S, S', u, v, integralSupportIntermediateSequence, integralSupportUnionMap,
        Category.assoc, biprod.lift_fst, biprod.map_fst, biprod.lift_fst_assoc,
        integralSupportRestriction_comp]
    · simp only [S, S', u, v, integralSupportIntermediateSequence, integralSupportUnionMap,
        Category.assoc, biprod.lift_snd, biprod.map_snd, biprod.lift_snd_assoc,
        integralSupportRestriction_comp]
  let hS' := integralSupportIntermediateSequence_shortExact K' L'
  letI := hS'.epi_g
  have hv : S'.f ≫ (v ≫ S.g) = 0 := by
    rw [← Category.assoc, ← huv, Category.assoc, S.zero, comp_zero]
  exact
    { τ₁ := u
      τ₂ := v
      τ₃ := hS'.exact.desc (v ≫ S.g) hv
      comm₁₂ := huv
      comm₂₃ := (hS'.exact.g_desc (v ≫ S.g) hv).symm }

theorem integralSupportIntermediateRestriction_comparison
    {K L K' L' : Set X} (hK : K ⊆ K') (hL : L ⊆ L') :
    (integralSupportIntermediateRestriction hK hL).τ₃ ≫
        integralSupportComparison K L =
      integralSupportComparison K' L' ≫
        integralSupportRestriction (inter_subset_inter hK hL) := by
  let S' := integralSupportIntermediateSequence K' L'
  let := (integralSupportIntermediateSequence_shortExact K' L').epi_g
  apply (cancel_epi S'.g).mp
  rw [← Category.assoc,
    ← (integralSupportIntermediateRestriction hK hL).comm₂₃,
    Category.assoc]
  change (integralSupportIntermediateRestriction hK hL).τ₂ ≫
      integralSumDifference Kᶜ Lᶜ ≫ integralSupportComparison K L =
    integralSumDifference K'ᶜ L'ᶜ ≫ integralSupportComparison K' L' ≫
      integralSupportRestriction (inter_subset_inter hK hL)
  rw [integralSupportComparison_difference, integralSupportComparison_difference_assoc]
  change biprod.map (integralSupportRestriction hK) (integralSupportRestriction hL) ≫
      integralSupportDifference K L =
    integralSupportDifference K' L' ≫ integralSupportRestriction (inter_subset_inter hK hL)
  apply biprod.hom_ext'
  · simp [integralSupportDifference, integralSupportRestriction_comp]
  · simp [integralSupportDifference, integralSupportRestriction_comp,
      Preadditive.comp_neg, Preadditive.neg_comp]

def integralDualShortComplexHom
    {S T : ShortComplex (ChainComplex (ModuleCat.{u} Int) Nat)} (f : S ⟶ T) :
    integralDualSequence T ⟶ integralDualSequence S where
  τ₁ := integralDualMap f.τ₃
  τ₂ := integralDualMap f.τ₂
  τ₃ := integralDualMap f.τ₁
  comm₁₂ := by
    change integralDualMap f.τ₃ ≫ integralDualMap S.g =
      integralDualMap T.g ≫ integralDualMap f.τ₂
    rw [← integralDualMap_comp, ← integralDualMap_comp, f.comm₂₃]
  comm₂₃ := by
    change integralDualMap f.τ₂ ≫ integralDualMap S.f =
      integralDualMap T.f ≫ integralDualMap f.τ₁
    rw [← integralDualMap_comp, ← integralDualMap_comp, f.comm₁₂]

def integralSupportDualEnlargement {K L K' L' : Set X}
    (hK : K ⊆ K') (hL : L ⊆ L') :
    integralSupportDualSequence K L ⟶ integralSupportDualSequence K' L' :=
  (integralSupportDualSequenceIso K L).inv ≫
    integralDualShortComplexHom (integralSupportIntermediateRestriction hK hL) ≫
      (integralSupportDualSequenceIso K' L').hom

@[reassoc]
theorem integralSupportCohomologyConnecting_naturality
    {K L K' L' : Set X} (hK : K ⊆ K') (hL : L ⊆ L')
    (hKC : IsClosed K) (hLC : IsClosed L)
    (hK'C : IsClosed K') (hL'C : IsClosed L') (q : Nat) :
    integralSupportCohomologyConnecting K L hKC hLC q ≫
        integralSupportCohomologyPushforward (inter_subset_inter hK hL) (q + 1) =
      integralSupportCohomologyPushforward (union_subset_union hK hL) q ≫
        integralSupportCohomologyConnecting K' L' hK'C hL'C q := by
  let φ := integralSupportDualEnlargement hK hL
  let e := integralSupportCohomologyIntersectionIso K L hKC hLC (q + 1)
  let e' := integralSupportCohomologyIntersectionIso K' L' hK'C hL'C (q + 1)
  have hφ₁ : φ.τ₁ = integralDualMap
      (integralSupportIntermediateRestriction hK hL).τ₃ := by
    change (𝟙 _ ≫ integralDualMap
      (integralSupportIntermediateRestriction hK hL).τ₃ ≫ 𝟙 _) = _
    simp only [Category.comp_id, Category.id_comp]
  have hφ₃ : φ.τ₃ = integralSupportCochainPushforward (union_subset_union hK hL) := by
    change (𝟙 _ ≫ integralSupportCochainPushforward
      (union_subset_union hK hL) ≫ 𝟙 _) = _
    simp only [Category.comp_id, Category.id_comp]
  have hn : e.hom ≫ homologyMap φ.τ₁ (q + 1) =
      integralSupportCohomologyPushforward (inter_subset_inter hK hL) (q + 1) ≫ e'.hom := by
    rw [hφ₁]
    change homologyMap (integralDualMap (integralSupportComparison K L)) (q + 1) ≫
        homologyMap (integralDualMap
          (integralSupportIntermediateRestriction hK hL).τ₃) (q + 1) =
      homologyMap (integralDualMap
          (integralSupportRestriction (inter_subset_inter hK hL))) (q + 1) ≫
        homologyMap (integralDualMap (integralSupportComparison K' L')) (q + 1)
    rw [← homologyMap_comp, ← homologyMap_comp, ← integralDualMap_comp,
      ← integralDualMap_comp, integralSupportIntermediateRestriction_comparison]
  have hn' : e.inv ≫
      integralSupportCohomologyPushforward (inter_subset_inter hK hL) (q + 1) =
        homologyMap φ.τ₁ (q + 1) ≫ e'.inv := by
    apply (cancel_epi e.hom).mp
    simp only [Iso.hom_inv_id_assoc]
    rw [← Category.assoc, hn, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hδ := HomologySequence.δ_naturality φ
    (integralSupportDualSequence_shortExact' K L)
    (integralSupportDualSequence_shortExact' K' L') q (q + 1) rfl
  change ((integralSupportDualSequence_shortExact' K L).δ q (q + 1) rfl ≫ e.inv) ≫
      integralSupportCohomologyPushforward (inter_subset_inter hK hL) (q + 1) =
    integralSupportCohomologyPushforward (union_subset_union hK hL) q ≫
      (integralSupportDualSequence_shortExact' K' L').δ q (q + 1) rfl ≫ e'.inv
  rw [Category.assoc, hn', ← Category.assoc, hδ, hφ₃]
  rfl

end PoincareConjecture.Proofs.M02.Topology
