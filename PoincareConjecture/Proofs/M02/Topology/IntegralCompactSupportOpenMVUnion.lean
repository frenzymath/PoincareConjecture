import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSupportOpenConnectingRefinement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits TopologicalSpace Set

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable {X : Type u} [TopologicalSpace X] [T2Space X]

set_option backward.isDefEq.respectTransparency false in
theorem exists_integralCompactSupportOpenSum_preimage
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (A : Compacts U) (B : Compacts V) (q : Nat)
    (a : integralSupportCohomology
      ((integralOpenSubtypeUnionInclusion U V hU) '' (A : Set U)) q)
    (b : integralSupportCohomology
      ((integralOpenSubtypeUnionInclusionRight U V hV) '' (B : Set V)) q) :
    ∃ y : (integralCompactSupportCohomology U q ⊞
        integralCompactSupportCohomology V q : ModuleCat.{u} Int),
      integralCompactSupportOpenSum U V hU hV q y =
        integralCompactSupportCohomologyClass
          (integralCompactSupportOpenPairUnion U V hU hV A B) q
          (integralSupportCohomologyPushforward subset_union_left q a +
            integralSupportCohomologyPushforward subset_union_right q b) := by
  let fU := integralOpenSubtypeUnionInclusion U V hU
  let fV := integralOpenSubtypeUnionInclusionRight U V hV
  let hfU := integralOpenSubtypeUnionInclusion_isOpenEmbedding U V hU hV
  let hfV := integralOpenSubtypeUnionInclusionRight_isOpenEmbedding U V hU hV
  let xA := integralCompactSupportCohomologyClass A q
    ((integralSupportOpenEmbeddingCohomologyIso fU hfU A q).hom a)
  let xB := integralCompactSupportCohomologyClass B q
    ((integralSupportOpenEmbeddingCohomologyIso fV hfV B q).hom b)
  let HU := integralCompactSupportCohomology U q
  let HV := integralCompactSupportCohomology V q
  refine ⟨(biprod.inl : HU ⟶ HU ⊞ HV).hom xA +
    (biprod.inr : HV ⟶ HU ⊞ HV).hom xB, ?_⟩
  have hU0 := congrArg (fun k => k.hom a)
    (integralCompactSupportCohomologyOpenMap_pullback_class fU hfU A q)
  have hV0 := congrArg (fun k => k.hom b)
    (integralCompactSupportCohomologyOpenMap_pullback_class fV hfV B q)
  have hsum : integralCompactSupportOpenSum U V hU hV q
      ((biprod.inl : HU ⟶ HU ⊞ HV).hom xA +
        (biprod.inr : HV ⟶ HU ⊞ HV).hom xB) =
      integralCompactSupportCohomologyClass (A.map fU fU.continuous) q a +
        integralCompactSupportCohomologyClass (B.map fV fV.continuous) q b := by
    rw [map_add]
    change ((biprod.inl : HU ⟶ HU ⊞ HV) ≫
        integralCompactSupportOpenSum U V hU hV q).hom xA +
      ((biprod.inr : HV ⟶ HU ⊞ HV) ≫
        integralCompactSupportOpenSum U V hU hV q).hom xB = _
    rw [integralCompactSupportOpenSum, biprod.inl_desc, biprod.inr_desc]
    exact congrArg₂ (fun x y => x + y) hU0 hV0
  let P := integralCompactSupportOpenPairUnion U V hU hV A B
  have hA := congrArg (fun k => k.hom a)
    (integralCompactSupportCohomologyClass_pushforward
      (show A.map fU fU.continuous ≤ P from subset_union_left) q)
  have hB := congrArg (fun k => k.hom b)
    (integralCompactSupportCohomologyClass_pushforward
      (show B.map fV fV.continuous ≤ P from subset_union_right) q)
  exact hsum.trans ((congrArg₂ (fun x y => x + y) hA.symm hB.symm).trans
    ((integralCompactSupportCohomologyClass P q).hom.map_add _ _).symm)

set_option backward.isDefEq.respectTransparency false in
theorem exists_integralCompactSupportOpenSum_preimage_of_stage_zero
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (A : Compacts U) (B : Compacts V) (q : Nat)
    (a : integralSupportCohomology
      (integralCompactSupportOpenPairUnion U V hU hV A B : Set ↥(U ∪ V)) q)
    (ha : integralCompactSupportOpenConnectingStage U V hU hV A B q a = 0) :
    ∃ y : (integralCompactSupportCohomology U q ⊞
        integralCompactSupportCohomology V q : ModuleCat.{u} Int),
      integralCompactSupportOpenSum U V hU hV q y =
        integralCompactSupportCohomologyClass
          (integralCompactSupportOpenPairUnion U V hU hV A B) q a := by
  obtain ⟨A', B', hA, hB, hzero⟩ :=
    exists_integralCompactSupportOpenConnectingStage_zero_refinement U V hU hV A B q a ha
  let K := A'.map (integralOpenSubtypeUnionInclusion U V hU)
    (integralOpenSubtypeUnionInclusion U V hU).continuous
  let L := B'.map (integralOpenSubtypeUnionInclusionRight U V hV)
    (integralOpenSubtypeUnionInclusionRight U V hV).continuous
  obtain ⟨aK, bL, hab⟩ := exists_integralSupportCohomology_union_pair_of_connecting_zero
    (K : Set ↥(U ∪ V)) (L : Set ↥(U ∪ V)) K.isCompact.isClosed L.isCompact.isClosed q
    (integralSupportCohomologyPushforward
      (integralCompactSupportOpenPairUnion_mono U V hU hV hA hB) q a) hzero
  obtain ⟨y, hy⟩ := exists_integralCompactSupportOpenSum_preimage U V hU hV A' B' q aK bL
  have hab' := congrArg (integralCompactSupportCohomologyClass
    (integralCompactSupportOpenPairUnion U V hU hV A' B') q).hom hab
  have hclass := congrArg (fun k => k.hom a)
    (integralCompactSupportCohomologyClass_pushforward
      (integralCompactSupportOpenPairUnion_mono U V hU hV hA hB) q)
  exact ⟨y, hy.trans (hab'.trans hclass)⟩

def integralCompactSupportOpenMayerVietorisUnion
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (q : Nat) :
    ShortComplex (ModuleCat.{u} Int) :=
  ShortComplex.mk (integralCompactSupportOpenSum U V hU hV q)
    (integralCompactSupportOpenConnecting U V hU hV q)
    (integralCompactSupportOpenSum_connecting U V hU hV q)

theorem integralCompactSupportOpenMayerVietoris_exact_union
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (q : Nat) :
    (integralCompactSupportOpenMayerVietorisUnion U V hU hV q).Exact := by
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro x hx
  obtain ⟨P, a, ha⟩ := exists_integralCompactSupportCohomology_representative q x
  obtain ⟨AB, hAB⟩ := exists_integralCompactSupportOpen_cover U V hU hV P
  have hc := congrArg (fun k => k.hom a)
    (integralCompactSupportOpenConnecting_class U V hU hV q P AB.1 AB.2 hAB)
  have hx' : integralCompactSupportOpenConnecting U V hU hV q
      (integralCompactSupportCohomologyClass P q a) = 0 :=
    (congrArg (integralCompactSupportOpenConnecting U V hU hV q).hom ha).trans hx
  have hz : integralCompactSupportOpenConnectingStage U V hU hV AB.1 AB.2 q
      (integralSupportCohomologyPushforward hAB q a) = 0 := hc.symm.trans hx'
  obtain ⟨y, hy⟩ := exists_integralCompactSupportOpenSum_preimage_of_stage_zero
    U V hU hV AB.1 AB.2 q (integralSupportCohomologyPushforward hAB q a) hz
  have hclass := congrArg (fun k => k.hom a)
    (integralCompactSupportCohomologyClass_pushforward hAB q)
  exact ⟨y, hy.trans (hclass.trans ha)⟩

end PoincareConjecture.Proofs.M02.Topology
