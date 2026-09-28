import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Cohomology.CompactSupport.MayerVietoris.IntegralCompactSupportOpenConnecting
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Cohomology.CompactSupport.Transport.IntegralCompactSupportRangeMapTransport
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Cohomology.Support.IntegralSupportCohomologyExactElements


set_option autoImplicit false

noncomputable section

open CategoryTheory Limits TopologicalSpace Set

universe u

namespace Poincare.Topology

variable {X : Type u} [TopologicalSpace X] [T2Space X]

set_option backward.isDefEq.respectTransparency false in
theorem integralCompactSupportOpenConnectingStage_left
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (A : Compacts U) (B : Compacts V) (q : Nat) :
    integralSupportCohomologyPushforward
        (subset_union_left :
          (A.map (integralOpenSubtypeUnionInclusion U V hU)
            (integralOpenSubtypeUnionInclusion U V hU).continuous : Set ↥(U ∪ V)) ⊆
          (integralCompactSupportOpenPairUnion U V hU hV A B : Set ↥(U ∪ V))) q ≫
        integralCompactSupportOpenConnectingStage U V hU hV A B q = 0 := by
  unfold integralCompactSupportOpenConnectingStage
  rw [← Category.assoc, integralSupportCohomologyUnionLeft_connecting, zero_comp]

set_option backward.isDefEq.respectTransparency false in
theorem integralCompactSupportOpenConnectingStage_right
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (A : Compacts U) (B : Compacts V) (q : Nat) :
    integralSupportCohomologyPushforward
        (subset_union_right :
          (B.map (integralOpenSubtypeUnionInclusionRight U V hV)
            (integralOpenSubtypeUnionInclusionRight U V hV).continuous : Set ↥(U ∪ V)) ⊆
          (integralCompactSupportOpenPairUnion U V hU hV A B : Set ↥(U ∪ V))) q ≫
        integralCompactSupportOpenConnectingStage U V hU hV A B q = 0 := by
  unfold integralCompactSupportOpenConnectingStage
  rw [← Category.assoc, integralSupportCohomologyUnionRight_connecting, zero_comp]

set_option backward.isDefEq.respectTransparency false in
theorem integralCompactSupportOpenUnionLeft_connecting
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (q : Nat) :
    integralCompactSupportCohomologyOpenMap (integralOpenSubtypeUnionInclusion U V hU)
        (integralOpenSubtypeUnionInclusion_isOpenEmbedding U V hU hV) q ≫
      integralCompactSupportOpenConnecting U V hU hV q = 0 := by
  apply integralCompactSupportCohomology_hom_ext q
  intro A
  rw [← Category.assoc, integralCompactSupportCohomologyOpenMap_class,
    Category.assoc,
    integralCompactSupportOpenConnecting_class U V hU hV q _ A ⊥ subset_union_left,
    ← Category.assoc, Category.assoc,
    integralCompactSupportOpenConnectingStage_left, comp_zero, comp_zero]

set_option backward.isDefEq.respectTransparency false in
theorem integralCompactSupportOpenUnionRight_connecting
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (q : Nat) :
    integralCompactSupportCohomologyOpenMap (integralOpenSubtypeUnionInclusionRight U V hV)
        (integralOpenSubtypeUnionInclusionRight_isOpenEmbedding U V hU hV) q ≫
      integralCompactSupportOpenConnecting U V hU hV q = 0 := by
  apply integralCompactSupportCohomology_hom_ext q
  intro B
  rw [← Category.assoc, integralCompactSupportCohomologyOpenMap_class,
    Category.assoc,
    integralCompactSupportOpenConnecting_class U V hU hV q _ ⊥ B subset_union_right,
    ← Category.assoc, Category.assoc,
    integralCompactSupportOpenConnectingStage_right, comp_zero, comp_zero]

@[reassoc]
theorem integralCompactSupportOpenSum_connecting
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (q : Nat) :
    integralCompactSupportOpenSum U V hU hV q ≫
      integralCompactSupportOpenConnecting U V hU hV q = 0 := by
  apply biprod.hom_ext'
  · rw [← Category.assoc, integralCompactSupportOpenSum, biprod.inl_desc,
      integralCompactSupportOpenUnionLeft_connecting, comp_zero]
  · rw [← Category.assoc, integralCompactSupportOpenSum, biprod.inr_desc,
      integralCompactSupportOpenUnionRight_connecting, comp_zero]

set_option backward.isDefEq.respectTransparency false in
theorem integralCompactSupportOpenConnectingStage_interLeft
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (A : Compacts U) (B : Compacts V) (q : Nat) :
    integralCompactSupportOpenConnectingStage U V hU hV A B q ≫
      integralCompactSupportCohomologyOpenMap (integralOpenSubtypeInclusion U V hU)
        (integralOpenSubtypeInclusion_isOpenEmbedding U V hU hV) (q + 1) = 0 := by
  unfold integralCompactSupportOpenConnectingStage
  rw [Category.assoc, integralCompactSupportCohomologyRangeMap_openMap
    (integralOpenSubtypeInclusion U V hU) (integralOpenSubtypeUnionInclusion U V hU)
    (integralOpenIntersectionUnionInclusion U V hU) _
    (integralOpenSubtypeUnionInclusion_isOpenEmbedding U V hU hV) _
    rfl _ _ A inter_subset_left,
    ← Category.assoc, integralSupportCohomologyConnecting_interLeft, zero_comp]

set_option backward.isDefEq.respectTransparency false in
theorem integralCompactSupportOpenConnectingStage_interRight
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (A : Compacts U) (B : Compacts V) (q : Nat) :
    integralCompactSupportOpenConnectingStage U V hU hV A B q ≫
      integralCompactSupportCohomologyOpenMap (integralOpenSubtypeInclusionRight U V hV)
        (integralOpenSubtypeInclusionRight_isOpenEmbedding U V hU hV) (q + 1) = 0 := by
  have heq : integralOpenIntersectionUnionInclusion U V hU =
      (integralOpenSubtypeUnionInclusionRight U V hV).comp
        (integralOpenSubtypeInclusionRight U V hV) := by
    ext x
    rfl
  unfold integralCompactSupportOpenConnectingStage
  rw [Category.assoc, integralCompactSupportCohomologyRangeMap_openMap
    (integralOpenSubtypeInclusionRight U V hV)
    (integralOpenSubtypeUnionInclusionRight U V hV)
    (integralOpenIntersectionUnionInclusion U V hU) _
    (integralOpenSubtypeUnionInclusionRight_isOpenEmbedding U V hU hV) _
    heq _ _ B inter_subset_right,
    ← Category.assoc, integralSupportCohomologyConnecting_interRight, zero_comp]

theorem integralCompactSupportOpenConnectingStage_difference
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (A : Compacts U) (B : Compacts V) (q : Nat) :
    integralCompactSupportOpenConnectingStage U V hU hV A B q ≫
      integralCompactSupportOpenDifference U V hU hV (q + 1) = 0 := by
  apply biprod.hom_ext
  · rw [Category.assoc, integralCompactSupportOpenDifference, biprod.lift_fst,
      integralCompactSupportOpenConnectingStage_interLeft, zero_comp]
  · rw [Category.assoc, integralCompactSupportOpenDifference, biprod.lift_snd,
      Preadditive.comp_neg, integralCompactSupportOpenConnectingStage_interRight,
      neg_zero, zero_comp]

@[reassoc]
theorem integralCompactSupportOpenConnecting_difference
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (q : Nat) :
    integralCompactSupportOpenConnecting U V hU hV q ≫
      integralCompactSupportOpenDifference U V hU hV (q + 1) = 0 := by
  apply integralCompactSupportCohomology_hom_ext q
  intro P
  obtain ⟨AB, hAB⟩ := exists_integralCompactSupportOpen_cover U V hU hV P
  rw [← Category.assoc,
    integralCompactSupportOpenConnecting_class U V hU hV q P AB.1 AB.2 hAB,
    Category.assoc, integralCompactSupportOpenConnectingStage_difference,
    comp_zero, comp_zero]

end Poincare.Topology
