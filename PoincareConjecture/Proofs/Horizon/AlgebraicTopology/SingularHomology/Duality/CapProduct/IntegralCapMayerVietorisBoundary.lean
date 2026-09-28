import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CapProduct.IntegralCapMayerVietoris








set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex Set

universe u

namespace Poincare.Topology

variable {X : Type u} [TopologicalSpace X]

def integralLocalizedCapPair (U K V L : Set X) (p q : Nat)
    (c : (integralChains X).X (p + q))
    (hc : c ∈ integralSmallChains (integralCommonCapCover U K V L) (p + q))
    (phi : (integralSupportCochains K).X q)
    (psi : (integralSupportCochains L).X q) :
    (integralChains U ⊞ integralChains V).X p :=
  (biprod.inl : integralChains U ⟶ integralChains U ⊞ integralChains V).f p
      (integralLocalizedCap U K p q c
        (integralCommonCapCover_small_left U K V L (p + q) hc) phi) +
    (biprod.inr : integralChains V ⟶ integralChains U ⊞ integralChains V).f p
      (integralLocalizedCap V L p q c
        (integralCommonCapCover_small_right U K V L (p + q) hc) psi)

theorem integralLocalizedCapPair_fst (U K V L : Set X) (p q : Nat)
    (c : (integralChains X).X (p + q))
    (hc : c ∈ integralSmallChains (integralCommonCapCover U K V L) (p + q))
    (phi : (integralSupportCochains K).X q)
    (psi : (integralSupportCochains L).X q) :
    (biprod.fst : integralChains U ⊞ integralChains V ⟶ integralChains U).f p
      (integralLocalizedCapPair U K V L p q c hc phi psi) =
    integralLocalizedCap U K p q c
      (integralCommonCapCover_small_left U K V L (p + q) hc) phi := by
  simp only [integralLocalizedCapPair, map_add, ← ModuleCat.comp_apply,
    biprod_inl_fst_f, biprod_inr_fst_f, ModuleCat.id_apply]
  exact add_zero _

theorem integralLocalizedCapPair_snd (U K V L : Set X) (p q : Nat)
    (c : (integralChains X).X (p + q))
    (hc : c ∈ integralSmallChains (integralCommonCapCover U K V L) (p + q))
    (phi : (integralSupportCochains K).X q)
    (psi : (integralSupportCochains L).X q) :
    (biprod.snd : integralChains U ⊞ integralChains V ⟶ integralChains V).f p
      (integralLocalizedCapPair U K V L p q c hc phi psi) =
    integralLocalizedCap V L p q c
      (integralCommonCapCover_small_right U K V L (p + q) hc) psi := by
  simp only [integralLocalizedCapPair, map_add, ← ModuleCat.comp_apply,
    biprod_inl_snd_f, biprod_inr_snd_f, ModuleCat.id_apply]
  exact zero_add _

private theorem chainPair_fst_d {C D : ChainComplex (ModuleCat.{u} Int) Nat}
    (p r : Nat) (b : (C ⊞ D).X p) :
    (biprod.fst : C ⊞ D ⟶ C).f r ((C ⊞ D).d p r b) =
      C.d p r ((biprod.fst : C ⊞ D ⟶ C).f p b) :=
  (congrArg (fun f => f b) ((biprod.fst : C ⊞ D ⟶ C).comm p r)).symm

private theorem chainPair_snd_d {C D : ChainComplex (ModuleCat.{u} Int) Nat}
    (p r : Nat) (b : (C ⊞ D).X p) :
    (biprod.snd : C ⊞ D ⟶ D).f r ((C ⊞ D).d p r b) =
      D.d p r ((biprod.snd : C ⊞ D ⟶ D).f p b) :=
  (congrArg (fun f => f b) ((biprod.snd : C ⊞ D ⟶ D).comm p r)).symm

private theorem openDifference_fst (U V : Set X) (p : Nat)
    (a : (integralChains ↥(U ∩ V)).X p) :
    (biprod.fst : integralChains U ⊞ integralChains V ⟶ integralChains U).f p
      ((integralOpenDifference U V).f p a) =
      (integralNestedChains (inter_subset_left : U ∩ V ⊆ U)).f p a :=
  congrArg (fun f => f.f p a)
    (show integralOpenDifference U V ≫ biprod.fst =
      integralNestedChains (inter_subset_left : U ∩ V ⊆ U) by
      simp [integralOpenDifference])

private theorem openDifference_snd (U V : Set X) (p : Nat)
    (a : (integralChains ↥(U ∩ V)).X p) :
    (biprod.snd : integralChains U ⊞ integralChains V ⟶ integralChains V).f p
      ((integralOpenDifference U V).f p a) =
      -((integralNestedChains (inter_subset_right : U ∩ V ⊆ V)).f p a) :=
  congrArg (fun f => f.f p a)
    (show integralOpenDifference U V ≫ biprod.snd =
      -integralNestedChains (inter_subset_right : U ∩ V ⊆ V) by
      simp [integralOpenDifference])

theorem integralLocalizedCapPair_three_one_boundary
    (U K V L : Set X) (c : (integralChains X).X 3)
    (hc : c ∈ integralSmallChains (integralCommonCapCover U K V L) 3)
    (hdc : (integralChains X).d 3 2 c ∈
      LinearMap.range ((integralSubspaceChains (K ∪ L)ᶜ).f 2).hom)
    (phi : (integralSupportCochains K).X 1)
    (psi : (integralSupportCochains L).X 1)
    (gamma : (integralSupportCochains (K ∩ L)).X 2)
    (hphi : (integralSupportCochains K).d 1 2 phi =
      (integralSupportCochainPushforward inter_subset_left).f 2 gamma)
    (hpsi : (integralSupportCochains L).d 1 2 psi =
      -((integralSupportCochainPushforward inter_subset_right).f 2 gamma)) :
    (integralOpenDifference U V).f 1
        (integralLocalizedCap (U ∩ V) (K ∩ L) 1 2 c
          (integralCommonCapCover_small_inter U K V L 3 hc) gamma) =
      (integralChains U ⊞ integralChains V).d 2 1
        (integralLocalizedCapPair U K V L 2 1 c hc phi psi) := by
  apply integralBiprod_component_ext
  · have hnest := integralLocalizedCap_nested
      (U := U ∩ V) (V := U) (K := K ∩ L) (L := K)
      inter_subset_left inter_subset_left 1 2 c
      (integralCommonCapCover_small_inter U K V L 3 hc)
      (integralCommonCapCover_small_left U K V L 3 hc) gamma
    have hboundary := integralLocalizedCap_three_one_boundary U K c
      (integralCommonCapCover_small_left U K V L 3 hc)
      (integralSubspaceChains_range_mono
        (compl_subset_compl.mpr subset_union_left) 2 hdc) phi
    rw [openDifference_fst, chainPair_fst_d, integralLocalizedCapPair_fst]
    rw [hnest, hboundary, hphi]
  · have hnest := integralLocalizedCap_nested
      (U := U ∩ V) (V := V) (K := K ∩ L) (L := L)
      inter_subset_right inter_subset_right 1 2 c
      (integralCommonCapCover_small_inter U K V L 3 hc)
      (integralCommonCapCover_small_right U K V L 3 hc) gamma
    have hboundary := integralLocalizedCap_three_one_boundary V L c
      (integralCommonCapCover_small_right U K V L 3 hc)
      (integralSubspaceChains_range_mono
        (compl_subset_compl.mpr subset_union_right) 2 hdc) psi
    rw [openDifference_snd, chainPair_snd_d, integralLocalizedCapPair_snd]
    rw [hnest, hboundary, hpsi]
    simp

theorem integralLocalizedCapPair_three_two_boundary
    (U K V L : Set X) (c : (integralChains X).X 3)
    (hc : c ∈ integralSmallChains (integralCommonCapCover U K V L) 3)
    (hdc : (integralChains X).d 3 2 c ∈
      LinearMap.range ((integralSubspaceChains (K ∪ L)ᶜ).f 2).hom)
    (phi : (integralSupportCochains K).X 2)
    (psi : (integralSupportCochains L).X 2)
    (gamma : (integralSupportCochains (K ∩ L)).X 3)
    (hphi : (integralSupportCochains K).d 2 3 phi =
      (integralSupportCochainPushforward inter_subset_left).f 3 gamma)
    (hpsi : (integralSupportCochains L).d 2 3 psi =
      -((integralSupportCochainPushforward inter_subset_right).f 3 gamma)) :
    (integralOpenDifference U V).f 0
        (-integralLocalizedCap (U ∩ V) (K ∩ L) 0 3 c
          (integralCommonCapCover_small_inter U K V L 3 hc) gamma) =
      (integralChains U ⊞ integralChains V).d 1 0
        (integralLocalizedCapPair U K V L 1 2 c hc phi psi) := by
  apply integralBiprod_component_ext
  · have hnest := integralLocalizedCap_nested
      (U := U ∩ V) (V := U) (K := K ∩ L) (L := K)
      inter_subset_left inter_subset_left 0 3 c
      (integralCommonCapCover_small_inter U K V L 3 hc)
      (integralCommonCapCover_small_left U K V L 3 hc) gamma
    have hboundary := integralLocalizedCap_three_two_boundary U K c
      (integralCommonCapCover_small_left U K V L 3 hc)
      (integralSubspaceChains_range_mono
        (compl_subset_compl.mpr subset_union_left) 2 hdc) phi
    rw [openDifference_fst, chainPair_fst_d, integralLocalizedCapPair_fst]
    rw [map_neg, hnest, hboundary, hphi]
  · have hnest := integralLocalizedCap_nested
      (U := U ∩ V) (V := V) (K := K ∩ L) (L := L)
      inter_subset_right inter_subset_right 0 3 c
      (integralCommonCapCover_small_inter U K V L 3 hc)
      (integralCommonCapCover_small_right U K V L 3 hc) gamma
    have hboundary := integralLocalizedCap_three_two_boundary V L c
      (integralCommonCapCover_small_right U K V L 3 hc)
      (integralSubspaceChains_range_mono
        (compl_subset_compl.mpr subset_union_right) 2 hdc) psi
    rw [openDifference_snd, chainPair_snd_d, integralLocalizedCapPair_snd]
    rw [map_neg, hnest, hboundary, hpsi]
    simp

end Poincare.Topology
