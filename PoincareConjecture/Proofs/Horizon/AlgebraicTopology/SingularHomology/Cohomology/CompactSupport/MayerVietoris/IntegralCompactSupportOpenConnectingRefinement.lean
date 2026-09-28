import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Cohomology.CompactSupport.MayerVietoris.IntegralCompactSupportOpenConnectingZero

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits TopologicalSpace Set

universe u

namespace Poincare.Topology

variable {X : Type u} [TopologicalSpace X] [T2Space X]

theorem exists_integralCompactSupportOpen_pair_enlargement
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (A : Compacts U) (B : Compacts V) (S : Compacts ↥(U ∩ V)) :
    ∃ (A' : Compacts U) (B' : Compacts V), A ≤ A' ∧ B ≤ B' ∧
      (integralOpenIntersectionUnionInclusion U V hU) '' (S : Set ↥(U ∩ V)) ⊆
        (integralCompactSupportOpenPairIntersection U V hU hV A' B' : Set ↥(U ∪ V)) := by
  refine ⟨A ⊔ S.map (integralOpenSubtypeInclusion U V hU)
    (integralOpenSubtypeInclusion U V hU).continuous,
    B ⊔ S.map (integralOpenSubtypeInclusionRight U V hV)
      (integralOpenSubtypeInclusionRight U V hV).continuous,
    le_sup_left, le_sup_left, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  constructor
  · exact ⟨integralOpenSubtypeInclusion U V hU x,
      Or.inr ⟨x, hx, rfl⟩, rfl⟩
  · exact ⟨integralOpenSubtypeInclusionRight U V hV x,
      Or.inr ⟨x, hx, rfl⟩, Subtype.ext rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem exists_integralCompactSupportOpenConnectingStage_zero_refinement
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (A : Compacts U) (B : Compacts V) (q : Nat)
    (a : integralSupportCohomology
      (integralCompactSupportOpenPairUnion U V hU hV A B : Set ↥(U ∪ V)) q)
    (ha : integralCompactSupportOpenConnectingStage U V hU hV A B q a = 0) :
    ∃ (A' : Compacts U) (B' : Compacts V) (hA : A ≤ A') (hB : B ≤ B'),
      integralSupportCohomologyConnecting
        (A'.map (integralOpenSubtypeUnionInclusion U V hU)
          (integralOpenSubtypeUnionInclusion U V hU).continuous : Set ↥(U ∪ V))
        (B'.map (integralOpenSubtypeUnionInclusionRight U V hV)
          (integralOpenSubtypeUnionInclusionRight U V hV).continuous : Set ↥(U ∪ V))
        (Compacts.isCompact _).isClosed (Compacts.isCompact _).isClosed q
        (integralSupportCohomologyPushforward
          (integralCompactSupportOpenPairUnion_mono U V hU hV hA hB) q a) = 0 := by
  let K := A.map (integralOpenSubtypeUnionInclusion U V hU)
    (integralOpenSubtypeUnionInclusion U V hU).continuous
  let L := B.map (integralOpenSubtypeUnionInclusionRight U V hV)
    (integralOpenSubtypeUnionInclusionRight U V hV).continuous
  let d := integralSupportCohomologyConnecting (K : Set ↥(U ∪ V)) (L : Set ↥(U ∪ V))
    K.isCompact.isClosed L.isCompact.isClosed q
  change integralCompactSupportCohomologyRangeMap
    (integralOpenIntersectionUnionInclusion U V hU)
    (integralOpenIntersectionUnionInclusion_isOpenEmbedding U V hU hV)
    (integralCompactSupportOpenPairIntersection U V hU hV A B)
    (integralCompactSupportOpenPairIntersection_subset_range U V hU hV A B) (q + 1)
    (d a) = 0 at ha
  obtain ⟨S, hRS, hzero⟩ :=
    (integralCompactSupportCohomologyRangeMap_eq_zero_iff _ _ _ _ _ _).mp ha
  obtain ⟨A', B', hA, hB, hS⟩ :=
    exists_integralCompactSupportOpen_pair_enlargement U V hU hV A B S
  refine ⟨A', B', hA, hB, ?_⟩
  let K' := A'.map (integralOpenSubtypeUnionInclusion U V hU)
    (integralOpenSubtypeUnionInclusion U V hU).continuous
  let L' := B'.map (integralOpenSubtypeUnionInclusionRight U V hV)
    (integralOpenSubtypeUnionInclusionRight U V hV).continuous
  have hK : (K : Set ↥(U ∪ V)) ⊆ K' := image_mono hA
  have hL : (L : Set ↥(U ∪ V)) ⊆ L' := image_mono hB
  have hn := congrArg (fun k => k.hom a)
    (integralSupportCohomologyConnecting_naturality hK hL
      K.isCompact.isClosed L.isCompact.isClosed K'.isCompact.isClosed L'.isCompact.isClosed q)
  have hz : integralSupportCohomologyPushforward
      (inter_subset_inter hK hL) (q + 1) (d a) = 0 := by
    have he := congrArg (fun k => k.hom (d a))
      (integralSupportCohomologyPushforward_comp hRS hS (q + 1))
    have h0 := congrArg (integralSupportCohomologyPushforward hS (q + 1)).hom hzero
    exact he.symm.trans (h0.trans (map_zero _))
  exact hn.symm.trans hz

end Poincare.Topology
