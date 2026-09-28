import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CapProduct.IntegralCapMayerVietorisBoundary
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CapProduct.IntegralLocalizedRelativeCap
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.MayerVietoris.IntegralMayerVietorisConnectingClass
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Relative.IntegralSmallRelativeRepresentative
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Cohomology.Support.IntegralSupportCohomologyLiftCorrection


set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex Set

universe u

namespace Poincare.Topology

variable {X : Type u} [TopologicalSpace X]

theorem integralSupportCochainSum_apply (K L : Set X) (q : Nat)
    (b : (integralSupportCochains K ⊞ integralSupportCochains L).X q) :
    (integralSupportCochainSum K L).f q b =
      (integralSupportCochainPushforward (subset_union_left : K ⊆ K ∪ L)).f q
          ((biprod.fst : integralSupportCochains K ⊞ integralSupportCochains L ⟶ _).f q b) +
        (integralSupportCochainPushforward (subset_union_right : L ⊆ K ∪ L)).f q
          ((biprod.snd : integralSupportCochains K ⊞ integralSupportCochains L ⟶ _).f q b) := by
  have h : integralSupportCochainSum K L =
      biprod.fst ≫ integralSupportCochainPushforward (subset_union_left : K ⊆ K ∪ L) +
        biprod.snd ≫ integralSupportCochainPushforward (subset_union_right : L ⊆ K ∪ L) := by
    apply biprod.hom_ext' <;> simp [integralSupportCochainSum, Preadditive.comp_add]
  exact congrArg (fun f => f.f q b) h

theorem integralLocalizedCapPair_sum_inclusion
    (U K V L : Set X) (p q : Nat) (c : (integralChains X).X (p + q))
    (hc : c ∈ integralSmallChains (integralCommonCapCover U K V L) (p + q))
    (b : (integralSupportCochains K ⊞ integralSupportCochains L).X q) :
    (integralSmallChainInclusion (integralBinaryCover U V)).f p
        ((integralOpenSum U V).f p
          (integralLocalizedCapPair U K V L p q c hc
            ((biprod.fst : integralSupportCochains K ⊞ integralSupportCochains L ⟶ _).f q b)
            ((biprod.snd : integralSupportCochains K ⊞ integralSupportCochains L ⟶ _).f q b))) =
      integralSupportCap (K ∪ L)ᶜ p q ((integralRelativeProjection (K ∪ L)ᶜ).f (p + q) c)
        ((integralSupportCochainSum K L).f q b) := by
  rw [integralOpenSum_inclusion_apply, integralLocalizedCapPair_fst,
    integralLocalizedCapPair_snd, integralLocalizedCap_inclusion,
    integralLocalizedCap_inclusion, integralSupportCap_projection,
    integralSupportCochainSum_apply, map_add, map_add,
    integralCochainPullback_pushforward, integralCochainPullback_pushforward]

theorem integralSupportCochainDifference_boundary_components
    (K L : Set X) (q : Nat)
    (b : (integralSupportCochains K ⊞ integralSupportCochains L).X q)
    (gamma : (integralSupportCochains (K ∩ L)).X (q + 1))
    (hb : (integralSupportCochainDifference K L).f (q + 1) gamma =
      (integralSupportCochains K ⊞ integralSupportCochains L).d q (q + 1) b) :
    (integralSupportCochains K).d q (q + 1)
        ((biprod.fst : integralSupportCochains K ⊞ integralSupportCochains L ⟶ _).f q b) =
      (integralSupportCochainPushforward (inter_subset_left : K ∩ L ⊆ K)).f (q + 1) gamma ∧
    (integralSupportCochains L).d q (q + 1)
        ((biprod.snd : integralSupportCochains K ⊞ integralSupportCochains L ⟶ _).f q b) =
      -((integralSupportCochainPushforward (inter_subset_right : K ∩ L ⊆ L)).f (q + 1) gamma) := by
  constructor
  · have he := congrArg
      ((biprod.fst : integralSupportCochains K ⊞ integralSupportCochains L ⟶ _).f (q + 1)) hb
    have hcomm := congrArg (fun f => f b)
      ((biprod.fst : integralSupportCochains K ⊞ integralSupportCochains L ⟶ _).comm q (q + 1))
    have hf := congrArg (fun f => f.f (q + 1) gamma)
      (show integralSupportCochainDifference K L ≫ biprod.fst =
        integralSupportCochainPushforward (inter_subset_left : K ∩ L ⊆ K) by
        simp [integralSupportCochainDifference])
    exact hcomm.trans (he.symm.trans hf)
  · have he := congrArg
      ((biprod.snd : integralSupportCochains K ⊞ integralSupportCochains L ⟶ _).f (q + 1)) hb
    have hcomm := congrArg (fun f => f b)
      ((biprod.snd : integralSupportCochains K ⊞ integralSupportCochains L ⟶ _).comm q (q + 1))
    have hf := congrArg (fun f => f.f (q + 1) gamma)
      (show integralSupportCochainDifference K L ≫ biprod.snd =
        -integralSupportCochainPushforward (inter_subset_right : K ∩ L ⊆ L) by
        simp [integralSupportCochainDifference])
    exact hcomm.trans (he.symm.trans hf)

private theorem openSum_cycle_of_boundary
    (U V : Set X) (n : Nat)
    (b : (integralChains U ⊞ integralChains V).X (n + 1))
    (a : (integralChains ↥(U ∩ V)).X n)
    (hb : (integralOpenDifference U V).f n a =
      (integralChains U ⊞ integralChains V).d (n + 1) n b) :
    (integralSmallChainComplex (integralBinaryCover U V)).d (n + 1) n
      ((integralOpenSum U V).f (n + 1) b) = 0 := by
  have hcomm := congrArg (fun f => f b) ((integralOpenSum U V).comm (n + 1) n)
  have hz := congrArg (fun f => f.f n a) (integralOpenDifference_sum U V)
  refine hcomm.trans ?_
  change (integralOpenSum U V).f n
    ((integralChains U ⊞ integralChains V).d (n + 1) n b) = 0
  rw [← hb]
  exact hz

theorem integralSupportCapHomologyOne_connecting_representative
    (U K V L : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ)
    (c : (integralChains X).X 3)
    (hc : c ∈ integralSmallChains (integralCommonCapCover U K V L) 3)
    (hdc : (integralChains X).d 3 2 c ∈
      LinearMap.range ((integralSubspaceChains (K ∪ L)ᶜ).f 2).hom)
    (z : LinearMap.ker ((integralRelativeChains (K ∪ L)ᶜ).sc' 4 3 2).g.hom)
    (hz : z.val = (integralRelativeProjection (K ∪ L)ᶜ).f 3 c)
    (phi : LinearMap.ker ((integralSupportCochains (K ∪ L)).sc' 0 1 2).g.hom)
    (b : (integralSupportCochains K ⊞ integralSupportCochains L).X 1)
    (hb : (integralSupportCochainSum K L).f 1 b = phi.val)
    (gamma : LinearMap.ker ((integralSupportCochains (K ∩ L)).sc' 1 2 3).g.hom)
    (hboundary : (integralSupportCochainDifference K L).f 2 gamma.val =
      (integralSupportCochains K ⊞ integralSupportCochains L).d 1 2 b) :
    integralOpenHomologyConnecting U V hU hV hcover 1
        (integralSupportCapHomologyOne (K ∪ L)ᶜ
          (moduleComplexHomologyClass (integralRelativeChains (K ∪ L)ᶜ)
            4 3 2 (by simp) (by simp) z)
          (moduleComplexHomologyClass (integralSupportCochains (K ∪ L))
            0 1 2 (by simp) (by simp) phi)) =
      moduleComplexHomologyClass (integralChains ↥(U ∩ V)) 2 1 0 (by simp) (by simp)
        ⟨integralLocalizedCap (U ∩ V) (K ∩ L) 1 2 c
          (integralCommonCapCover_small_inter U K V L 3 hc) gamma.val,
          integralLocalizedCap_three_two_cycle (U ∩ V) (K ∩ L) c
            (integralCommonCapCover_small_inter U K V L 3 hc)
            (integralSubspaceChains_range_mono
              (compl_subset_compl.mpr (inter_subset_left.trans subset_union_left)) 2 hdc)
            gamma.val gamma.property⟩ := by
  obtain ⟨hleft, hright⟩ := integralSupportCochainDifference_boundary_components
    K L 1 b gamma.val hboundary
  let p := integralLocalizedCapPair U K V L 2 1 c hc
    ((biprod.fst : integralSupportCochains K ⊞ integralSupportCochains L ⟶ _).f 1 b)
    ((biprod.snd : integralSupportCochains K ⊞ integralSupportCochains L ⟶ _).f 1 b)
  let a := integralLocalizedCap (U ∩ V) (K ∩ L) 1 2 c
    (integralCommonCapCover_small_inter U K V L 3 hc) gamma.val
  have hp : (integralOpenDifference U V).f 1 a =
      (integralChains U ⊞ integralChains V).d 2 1 p :=
    integralLocalizedCapPair_three_one_boundary U K V L c hc hdc _ _ gamma.val hleft hright
  let s : LinearMap.ker
      ((integralSmallChainComplex (integralBinaryCover U V)).sc' 3 2 1).g.hom :=
    ⟨(integralOpenSum U V).f 2 p, openSum_cycle_of_boundary U V 1 p a hp⟩
  have hs : homologyMap (integralSmallChainInclusion (integralBinaryCover U V)) 2
      (moduleComplexHomologyClass _ 3 2 1 (by simp) (by simp) s) =
      integralSupportCapHomologyOne (K ∪ L)ᶜ
        (moduleComplexHomologyClass _ 4 3 2 (by simp) (by simp) z)
        (moduleComplexHomologyClass _ 0 1 2 (by simp) (by simp) phi) := by
    rw [moduleComplexHomologyClass_map]
    simp only [moduleComplexHomologyClass]
    rw [integralSupportCapHomologyOne_class]
    congr 2
    apply Subtype.ext
    change (integralSmallChainInclusion (integralBinaryCover U V)).f 2
      ((integralOpenSum U V).f 2 p) = integralSupportCap (K ∪ L)ᶜ 2 1 z.val phi.val
    rw [hz, ← hb]
    exact integralLocalizedCapPair_sum_inclusion U K V L 2 1 c hc b
  rw [← hs]
  exact integralOpenHomologyConnecting_class U V hU hV hcover 1 s p rfl _ hp

theorem integralSupportCapHomologyOne_connecting
    (U K V L : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hK : IsClosed K) (hL : IsClosed L) (hKU : K ⊆ U) (hLV : L ⊆ V)
    (hcover : U ∪ V = univ)
    (z : integralSupportHomology (K ∪ L) 3)
    (phi : integralSupportCohomology (K ∪ L) 1) :
    integralOpenHomologyConnecting U V hU hV hcover 1
        (integralSupportCapHomologyOne (K ∪ L)ᶜ z phi) =
      integralSupportCapHomologyTwo ((Subtype.val : ↥(U ∩ V) → X) ⁻¹' (K ∩ L)ᶜ)
        ((integralOpenSupportHomologyIso (K ∩ L) (U ∩ V) (hK.inter hL)
          (hU.inter hV) (inter_subset_inter hKU hLV) 3).inv
            (integralSupportHomologyRestriction
              (inter_subset_left.trans subset_union_left : K ∩ L ⊆ K ∪ L) 3 z))
        (homologyMap (integralDualMap (integralOpenSupportMap (K ∩ L) (U ∩ V))) 2
          (integralSupportCohomologyConnecting K L hK hL 1 phi)) := by
  obtain ⟨c, hc, hdc, hzcycle, hclass⟩ := exists_integralSmallRelativeRepresentative_three
    (integralCommonCapCover U K V L) (integralCommonCapCover_open U K V L hU hK hV hL)
    (integralCommonCapCover_covers U K V L hKU hLV) (K ∪ L)ᶜ z
  obtain ⟨phic, hphi⟩ := moduleComplexHomologyClass_surjective
    (integralSupportCochains (K ∪ L)) 0 1 2 (by simp) (by simp) phi
  obtain ⟨b, gamma, hb, hgamma, hboundary⟩ := exists_integralSupportCohomology_corrected_lift
    K L hK hL 1 phic.val phic.property
  let zc : LinearMap.ker ((integralRelativeChains (K ∪ L)ᶜ).sc' 4 3 2).g.hom :=
    ⟨(integralRelativeProjection (K ∪ L)ᶜ).f 3 c, hzcycle⟩
  let gc : LinearMap.ker ((integralSupportCochains (K ∩ L)).sc' 1 2 3).g.hom :=
    ⟨gamma, hgamma⟩
  let f := integralSupportRestriction
    (inter_subset_left.trans subset_union_left : K ∩ L ⊆ K ∪ L)
  let zi := moduleHomologyCycleMap
    ((shortComplexFunctor' (ModuleCat.{u} Int) (ComplexShape.down Nat) 4 3 2).map f) zc
  have hzi : zi.val = (integralRelativeProjection (K ∩ L)ᶜ).f 3 c :=
    congrArg (fun f => f.f 3 c) (integralSupportRestriction_projection
      (inter_subset_left.trans subset_union_left : K ∩ L ⊆ K ∪ L))
  have hzclass : integralSupportHomologyRestriction
      (inter_subset_left.trans subset_union_left : K ∩ L ⊆ K ∪ L) 3 z =
      moduleComplexHomologyClass (integralRelativeChains (K ∩ L)ᶜ)
        4 3 2 (by simp) (by simp) zi := by
    rw [← hclass]
    exact moduleComplexHomologyClass_map f 4 3 2 (by simp) (by simp) zc
  have hdelta : integralSupportCohomologyConnecting K L hK hL 1 phi =
      moduleComplexHomologyClass (integralSupportCochains (K ∩ L))
        1 2 3 (by simp) (by simp) gc := by
    rw [← hphi]
    exact integralSupportCohomologyConnecting_class K L hK hL 0 phic b hb gc hboundary
  rw [hzclass, hdelta]
  rw [integralLocalizedCapHomologyTwo_class (U ∩ V) (K ∩ L) (hU.inter hV)
    (hK.inter hL) (inter_subset_inter hKU hLV) c
    (integralCommonCapCover_small_inter U K V L 3 hc)
    (integralSubspaceChains_range_mono
      (compl_subset_compl.mpr (inter_subset_left.trans subset_union_left)) 2 hdc) zi hzi gc]
  rw [← hclass, ← hphi]
  exact integralSupportCapHomologyOne_connecting_representative
    U K V L hU hV hcover c hc hdc zc rfl phic b hb gc hboundary

theorem integralSupportCapHomologyTwo_connecting_representative
    (U K V L : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ)
    (c : (integralChains X).X 3)
    (hc : c ∈ integralSmallChains (integralCommonCapCover U K V L) 3)
    (hdc : (integralChains X).d 3 2 c ∈
      LinearMap.range ((integralSubspaceChains (K ∪ L)ᶜ).f 2).hom)
    (z : LinearMap.ker ((integralRelativeChains (K ∪ L)ᶜ).sc' 4 3 2).g.hom)
    (hz : z.val = (integralRelativeProjection (K ∪ L)ᶜ).f 3 c)
    (phi : LinearMap.ker ((integralSupportCochains (K ∪ L)).sc' 1 2 3).g.hom)
    (b : (integralSupportCochains K ⊞ integralSupportCochains L).X 2)
    (hb : (integralSupportCochainSum K L).f 2 b = phi.val)
    (gamma : LinearMap.ker ((integralSupportCochains (K ∩ L)).sc' 2 3 4).g.hom)
    (hboundary : (integralSupportCochainDifference K L).f 3 gamma.val =
      (integralSupportCochains K ⊞ integralSupportCochains L).d 2 3 b) :
    integralOpenHomologyConnecting U V hU hV hcover 0
        (integralSupportCapHomologyTwo (K ∪ L)ᶜ
          (moduleComplexHomologyClass (integralRelativeChains (K ∪ L)ᶜ)
            4 3 2 (by simp) (by simp) z)
          (moduleComplexHomologyClass (integralSupportCochains (K ∪ L))
            1 2 3 (by simp) (by simp) phi)) =
      -moduleComplexHomologyClass (integralChains ↥(U ∩ V)) 1 0 0 (by simp) (by simp)
        ⟨integralLocalizedCap (U ∩ V) (K ∩ L) 0 3 c
          (integralCommonCapCover_small_inter U K V L 3 hc) gamma.val, by
          change (integralChains ↥(U ∩ V)).d 0 0 _ = 0
          rw [(integralChains ↥(U ∩ V)).shape 0 0 (by simp)]
          rfl⟩ := by
  obtain ⟨hleft, hright⟩ := integralSupportCochainDifference_boundary_components
    K L 2 b gamma.val hboundary
  let p := integralLocalizedCapPair U K V L 1 2 c hc
    ((biprod.fst : integralSupportCochains K ⊞ integralSupportCochains L ⟶ _).f 2 b)
    ((biprod.snd : integralSupportCochains K ⊞ integralSupportCochains L ⟶ _).f 2 b)
  let a : LinearMap.ker ((integralChains ↥(U ∩ V)).sc' 1 0 0).g.hom :=
    ⟨integralLocalizedCap (U ∩ V) (K ∩ L) 0 3 c
      (integralCommonCapCover_small_inter U K V L 3 hc) gamma.val, by
      change (integralChains ↥(U ∩ V)).d 0 0 _ = 0
      rw [(integralChains ↥(U ∩ V)).shape 0 0 (by simp)]
      rfl⟩
  have hp : (integralOpenDifference U V).f 0 (-a.val) =
      (integralChains U ⊞ integralChains V).d 1 0 p :=
    integralLocalizedCapPair_three_two_boundary U K V L c hc hdc _ _ gamma.val hleft hright
  let s : LinearMap.ker
      ((integralSmallChainComplex (integralBinaryCover U V)).sc' 2 1 0).g.hom :=
    ⟨(integralOpenSum U V).f 1 p, openSum_cycle_of_boundary U V 0 p (-a.val) hp⟩
  have hs : homologyMap (integralSmallChainInclusion (integralBinaryCover U V)) 1
      (moduleComplexHomologyClass _ 2 1 0 (by simp) (by simp) s) =
      integralSupportCapHomologyTwo (K ∪ L)ᶜ
        (moduleComplexHomologyClass _ 4 3 2 (by simp) (by simp) z)
        (moduleComplexHomologyClass _ 1 2 3 (by simp) (by simp) phi) := by
    rw [moduleComplexHomologyClass_map]
    simp only [moduleComplexHomologyClass]
    rw [integralSupportCapHomologyTwo_class]
    congr 2
    apply Subtype.ext
    change (integralSmallChainInclusion (integralBinaryCover U V)).f 1
      ((integralOpenSum U V).f 1 p) = integralSupportCap (K ∪ L)ᶜ 1 2 z.val phi.val
    rw [hz, ← hb]
    exact integralLocalizedCapPair_sum_inclusion U K V L 1 2 c hc b
  rw [← hs]
  have he := integralOpenHomologyConnecting_class U V hU hV hcover 0 s p rfl (-a) hp
  refine he.trans ?_
  change moduleComplexHomologyClass _ 1 0 0 (by simp) (by simp) (-a) =
    -moduleComplexHomologyClass _ 1 0 0 (by simp) (by simp) a
  exact map_neg
    ((((integralChains ↥(U ∩ V)).sc' 1 0 0).moduleCatLeftHomologyData.π ≫
      ((integralChains ↥(U ∩ V)).sc' 1 0 0).moduleCatHomologyIso.inv ≫
      ((integralChains ↥(U ∩ V)).homologyIsoSc' 1 0 0 (by simp) (by simp)).inv).hom) a

theorem integralSupportCapHomologyTwo_connecting
    (U K V L : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hK : IsClosed K) (hL : IsClosed L) (hKU : K ⊆ U) (hLV : L ⊆ V)
    (hcover : U ∪ V = univ)
    (z : integralSupportHomology (K ∪ L) 3)
    (phi : integralSupportCohomology (K ∪ L) 2) :
    integralOpenHomologyConnecting U V hU hV hcover 0
        (integralSupportCapHomologyTwo (K ∪ L)ᶜ z phi) =
      -integralSupportCapHomologyThree ((Subtype.val : ↥(U ∩ V) → X) ⁻¹' (K ∩ L)ᶜ)
        ((integralOpenSupportHomologyIso (K ∩ L) (U ∩ V) (hK.inter hL)
          (hU.inter hV) (inter_subset_inter hKU hLV) 3).inv
            (integralSupportHomologyRestriction
              (inter_subset_left.trans subset_union_left : K ∩ L ⊆ K ∪ L) 3 z))
        (homologyMap (integralDualMap (integralOpenSupportMap (K ∩ L) (U ∩ V))) 3
          (integralSupportCohomologyConnecting K L hK hL 2 phi)) := by
  obtain ⟨c, hc, hdc, hzcycle, hclass⟩ := exists_integralSmallRelativeRepresentative_three
    (integralCommonCapCover U K V L) (integralCommonCapCover_open U K V L hU hK hV hL)
    (integralCommonCapCover_covers U K V L hKU hLV) (K ∪ L)ᶜ z
  obtain ⟨phic, hphi⟩ := moduleComplexHomologyClass_surjective
    (integralSupportCochains (K ∪ L)) 1 2 3 (by simp) (by simp) phi
  obtain ⟨b, gamma, hb, hgamma, hboundary⟩ := exists_integralSupportCohomology_corrected_lift
    K L hK hL 2 phic.val phic.property
  let zc : LinearMap.ker ((integralRelativeChains (K ∪ L)ᶜ).sc' 4 3 2).g.hom :=
    ⟨(integralRelativeProjection (K ∪ L)ᶜ).f 3 c, hzcycle⟩
  let gc : LinearMap.ker ((integralSupportCochains (K ∩ L)).sc' 2 3 4).g.hom :=
    ⟨gamma, hgamma⟩
  let f := integralSupportRestriction
    (inter_subset_left.trans subset_union_left : K ∩ L ⊆ K ∪ L)
  let zi := moduleHomologyCycleMap
    ((shortComplexFunctor' (ModuleCat.{u} Int) (ComplexShape.down Nat) 4 3 2).map f) zc
  have hzi : zi.val = (integralRelativeProjection (K ∩ L)ᶜ).f 3 c :=
    congrArg (fun f => f.f 3 c) (integralSupportRestriction_projection
      (inter_subset_left.trans subset_union_left : K ∩ L ⊆ K ∪ L))
  have hzclass : integralSupportHomologyRestriction
      (inter_subset_left.trans subset_union_left : K ∩ L ⊆ K ∪ L) 3 z =
      moduleComplexHomologyClass (integralRelativeChains (K ∩ L)ᶜ)
        4 3 2 (by simp) (by simp) zi := by
    rw [← hclass]
    exact moduleComplexHomologyClass_map f 4 3 2 (by simp) (by simp) zc
  have hdelta : integralSupportCohomologyConnecting K L hK hL 2 phi =
      moduleComplexHomologyClass (integralSupportCochains (K ∩ L))
        2 3 4 (by simp) (by simp) gc := by
    rw [← hphi]
    exact integralSupportCohomologyConnecting_class K L hK hL 1 phic b hb gc hboundary
  rw [hzclass, hdelta]
  rw [integralLocalizedCapHomologyThree_class (U ∩ V) (K ∩ L) (hU.inter hV)
    (hK.inter hL) (inter_subset_inter hKU hLV) c
    (integralCommonCapCover_small_inter U K V L 3 hc)
    (integralSubspaceChains_range_mono
      (compl_subset_compl.mpr (inter_subset_left.trans subset_union_left)) 2 hdc) zi hzi gc]
  rw [← hclass, ← hphi]
  exact integralSupportCapHomologyTwo_connecting_representative
    U K V L hU hV hcover c hc hdc zc rfl phic b hb gc hboundary

end Poincare.Topology
