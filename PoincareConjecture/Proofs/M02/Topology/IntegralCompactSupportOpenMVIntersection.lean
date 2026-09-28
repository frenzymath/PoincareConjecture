import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSupportOpenMVUnion
import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSupportOpenKernel



set_option autoImplicit false

noncomputable section

open CategoryTheory Limits TopologicalSpace Set

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable {X : Type u} [TopologicalSpace X] [T2Space X]

set_option backward.isDefEq.respectTransparency false in
theorem exists_integralCompactSupportOpenConnecting_preimage_of_pair_zero
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (q : Nat)
    (R : Compacts ↥(U ∪ V))
    (hR : (R : Set ↥(U ∪ V)) ⊆ Set.range (integralOpenIntersectionUnionInclusion U V hU))
    (A : Compacts U) (B : Compacts V)
    (hRA : (R : Set ↥(U ∪ V)) ⊆
      (integralOpenSubtypeUnionInclusion U V hU) '' (A : Set U))
    (hRB : (R : Set ↥(U ∪ V)) ⊆
      (integralOpenSubtypeUnionInclusionRight U V hV) '' (B : Set V))
    (c : integralSupportCohomology (R : Set ↥(U ∪ V)) (q + 1))
    (hcA : integralSupportCohomologyPushforward hRA (q + 1) c = 0)
    (hcB : integralSupportCohomologyPushforward hRB (q + 1) c = 0) :
    ∃ x : integralCompactSupportCohomology ↥(U ∪ V) q,
      integralCompactSupportOpenConnecting U V hU hV q x =
        integralCompactSupportCohomologyRangeMap
          (integralOpenIntersectionUnionInclusion U V hU)
          (integralOpenIntersectionUnionInclusion_isOpenEmbedding U V hU hV) R hR (q + 1) c := by
  let K := A.map (integralOpenSubtypeUnionInclusion U V hU)
    (integralOpenSubtypeUnionInclusion U V hU).continuous
  let L := B.map (integralOpenSubtypeUnionInclusionRight U V hV)
    (integralOpenSubtypeUnionInclusionRight U V hV).continuous
  have hRI : (R : Set ↥(U ∪ V)) ⊆ (K : Set ↥(U ∪ V)) ∩ L :=
    subset_inter hRA hRB
  let c' := integralSupportCohomologyPushforward hRI (q + 1) c
  have hK : integralSupportCohomologyPushforward
      (inter_subset_left : (K : Set ↥(U ∪ V)) ∩ L ⊆ K) (q + 1) c' = 0 := by
    exact (congrArg (fun k => k.hom c)
      (integralSupportCohomologyPushforward_comp hRI inter_subset_left (q + 1))).trans hcA
  have hL : integralSupportCohomologyPushforward
      (inter_subset_right : (K : Set ↥(U ∪ V)) ∩ L ⊆ L) (q + 1) c' = 0 := by
    exact (congrArg (fun k => k.hom c)
      (integralSupportCohomologyPushforward_comp hRI inter_subset_right (q + 1))).trans hcB
  obtain ⟨a, ha⟩ := exists_integralSupportCohomology_connecting_preimage
    (K : Set ↥(U ∪ V)) (L : Set ↥(U ∪ V)) K.isCompact.isClosed L.isCompact.isClosed
    q c' hK hL
  refine ⟨integralCompactSupportCohomologyClass
    (integralCompactSupportOpenPairUnion U V hU hV A B) q a, ?_⟩
  have hclass := congrArg (fun k => k.hom a)
    (integralCompactSupportOpenConnecting_pair_class U V hU hV q A B)
  have hstage := congrArg (integralCompactSupportCohomologyRangeMap
    (integralOpenIntersectionUnionInclusion U V hU)
    (integralOpenIntersectionUnionInclusion_isOpenEmbedding U V hU hV)
    (integralCompactSupportOpenPairIntersection U V hU hV A B)
    (integralCompactSupportOpenPairIntersection_subset_range U V hU hV A B) (q + 1)).hom ha
  have hn := congrArg (fun k => k.hom c)
    (integralCompactSupportCohomologyRangeMap_naturality
      (integralOpenIntersectionUnionInclusion U V hU)
      (integralOpenIntersectionUnionInclusion_isOpenEmbedding U V hU hV)
      (show R ≤ integralCompactSupportOpenPairIntersection U V hU hV A B from hRI)
      hR (integralCompactSupportOpenPairIntersection_subset_range U V hU hV A B) (q + 1))
  exact hclass.trans (hstage.trans hn)

set_option backward.isDefEq.respectTransparency false in
theorem exists_integralCompactSupportOpenConnecting_preimage
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (q : Nat)
    (z : integralCompactSupportCohomology ↥(U ∩ V) (q + 1))
    (hzU : integralCompactSupportCohomologyOpenMap
      (integralOpenSubtypeInclusion U V hU)
      (integralOpenSubtypeInclusion_isOpenEmbedding U V hU hV) (q + 1) z = 0)
    (hzV : integralCompactSupportCohomologyOpenMap
      (integralOpenSubtypeInclusionRight U V hV)
      (integralOpenSubtypeInclusionRight_isOpenEmbedding U V hU hV) (q + 1) z = 0) :
    ∃ x : integralCompactSupportCohomology ↥(U ∪ V) q,
      integralCompactSupportOpenConnecting U V hU hV q x = z := by
  let t := integralOpenIntersectionUnionInclusion U V hU
  let ht := integralOpenIntersectionUnionInclusion_isOpenEmbedding U V hU hV
  obtain ⟨S, c, hc⟩ := exists_integralCompactSupportCohomology_range_representative t ht (q + 1) z
  let R := S.map t t.continuous
  have hR : (R : Set ↥(U ∪ V)) ⊆ Set.range t := image_subset_range _ _
  let iU := integralOpenSubtypeInclusion U V hU
  let iV := integralOpenSubtypeInclusionRight U V hV
  let gU := integralOpenSubtypeUnionInclusion U V hU
  let gV := integralOpenSubtypeUnionInclusionRight U V hV
  let A := S.map iU iU.continuous
  let B := S.map iV iV.continuous
  have hRA : (R : Set ↥(U ∪ V)) ⊆ gU '' (A : Set U) := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨iU x, ⟨x, hx, rfl⟩, rfl⟩
  have hRB : (R : Set ↥(U ∪ V)) ⊆ gV '' (B : Set V) := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨iV x, ⟨x, hx, rfl⟩, Subtype.ext rfl⟩
  have heq : t = gV.comp iV := by
    ext x
    rfl
  obtain ⟨A', hA, hzeroA⟩ :=
    exists_integralCompactSupportCohomology_pushforward_zero_of_openMap_rangeMap_zero
      iU gU t (integralOpenSubtypeInclusion_isOpenEmbedding U V hU hV)
      (integralOpenSubtypeUnionInclusion_isOpenEmbedding U V hU hV) ht rfl R hR A hRA (q + 1) c
      ((congrArg (integralCompactSupportCohomologyOpenMap iU
        (integralOpenSubtypeInclusion_isOpenEmbedding U V hU hV) (q + 1)).hom hc).trans hzU)
  obtain ⟨B', hB, hzeroB⟩ :=
    exists_integralCompactSupportCohomology_pushforward_zero_of_openMap_rangeMap_zero
      iV gV t (integralOpenSubtypeInclusionRight_isOpenEmbedding U V hU hV)
      (integralOpenSubtypeUnionInclusionRight_isOpenEmbedding U V hU hV) ht heq R hR B hRB (q + 1) c
      ((congrArg (integralCompactSupportCohomologyOpenMap iV
        (integralOpenSubtypeInclusionRight_isOpenEmbedding U V hU hV) (q + 1)).hom hc).trans hzV)
  obtain ⟨x, hx⟩ := exists_integralCompactSupportOpenConnecting_preimage_of_pair_zero
    U V hU hV q R hR A' B' (hRA.trans (image_mono hA)) (hRB.trans (image_mono hB))
    c hzeroA hzeroB
  exact ⟨x, hx.trans hc⟩

def integralCompactSupportOpenMayerVietorisIntersection
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (q : Nat) :
    ShortComplex (ModuleCat.{u} Int) :=
  ShortComplex.mk (integralCompactSupportOpenConnecting U V hU hV q)
    (integralCompactSupportOpenDifference U V hU hV (q + 1))
    (integralCompactSupportOpenConnecting_difference U V hU hV q)

theorem integralCompactSupportOpenMayerVietoris_exact_intersection
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (q : Nat) :
    (integralCompactSupportOpenMayerVietorisIntersection U V hU hV q).Exact := by
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro z hz
  let HU := integralCompactSupportCohomology U (q + 1)
  let HV := integralCompactSupportCohomology V (q + 1)
  have hU0 := congrArg (biprod.fst : HU ⊞ HV ⟶ HU).hom hz
  have hV0 := congrArg (biprod.snd : HU ⊞ HV ⟶ HV).hom hz
  change (integralCompactSupportOpenDifference U V hU hV (q + 1) ≫ biprod.fst).hom z =
    (biprod.fst : HU ⊞ HV ⟶ HU).hom 0 at hU0
  change (integralCompactSupportOpenDifference U V hU hV (q + 1) ≫ biprod.snd).hom z =
    (biprod.snd : HU ⊞ HV ⟶ HV).hom 0 at hV0
  rw [integralCompactSupportOpenDifference, biprod.lift_fst, map_zero] at hU0
  rw [integralCompactSupportOpenDifference, biprod.lift_snd, map_zero] at hV0
  have hV1 : integralCompactSupportCohomologyOpenMap
      (integralOpenSubtypeInclusionRight U V hV)
      (integralOpenSubtypeInclusionRight_isOpenEmbedding U V hU hV) (q + 1) z = 0 := by
    change -(integralCompactSupportCohomologyOpenMap
      (integralOpenSubtypeInclusionRight U V hV)
      (integralOpenSubtypeInclusionRight_isOpenEmbedding U V hU hV) (q + 1)).hom z = 0 at hV0
    exact neg_eq_zero.mp hV0
  exact exists_integralCompactSupportOpenConnecting_preimage U V hU hV q z hU0 hV1

end PoincareConjecture.Proofs.M02.Topology
