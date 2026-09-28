import PoincareConjecture.Proofs.M02.Topology.IntegralCompactCohomologyOpenMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits TopologicalSpace Set

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable {X : Type u} [TopologicalSpace X]

def integralOpenSubtypeVal (U : Set X) : ContinuousMap U X :=
  ⟨Subtype.val, continuous_subtype_val⟩

def integralOpenSubtypeInclusion (U V : Set X) (hU : IsOpen U) :
    ContinuousMap ↥(U ∩ V) U :=
  ⟨fun x => ⟨x.1, x.2.1⟩, by
    exact hU.isOpenEmbedding_subtypeVal.isEmbedding.continuous_iff.mpr
      continuous_subtype_val⟩

def integralOpenSubtypeInclusionRight (U V : Set X) (hV : IsOpen V) :
    ContinuousMap ↥(U ∩ V) V :=
  ⟨fun x => ⟨x.1, x.2.2⟩, by
    exact hV.isOpenEmbedding_subtypeVal.isEmbedding.continuous_iff.mpr
      continuous_subtype_val⟩

theorem integralOpenSubtypeVal_isOpenEmbedding
    (U : Set X) (hU : IsOpen U) :
    _root_.Topology.IsOpenEmbedding (integralOpenSubtypeVal U) := by
  exact hU.isOpenEmbedding_subtypeVal

theorem integralOpenSubtypeInclusion_isOpenEmbedding
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) :
    _root_.Topology.IsOpenEmbedding (integralOpenSubtypeInclusion U V hU) := by
  apply _root_.Topology.IsOpenEmbedding.of_comp
    (integralOpenSubtypeInclusion U V hU)
    (integralOpenSubtypeVal_isOpenEmbedding U hU)
  change _root_.Topology.IsOpenEmbedding
    ((integralOpenSubtypeVal U).comp (integralOpenSubtypeInclusion U V hU))
  change _root_.Topology.IsOpenEmbedding (integralOpenSubtypeVal (U ∩ V))
  exact (hU.inter hV).isOpenEmbedding_subtypeVal

theorem integralOpenSubtypeInclusionRight_isOpenEmbedding
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) :
    _root_.Topology.IsOpenEmbedding (integralOpenSubtypeInclusionRight U V hV) := by
  apply _root_.Topology.IsOpenEmbedding.of_comp
    (integralOpenSubtypeInclusionRight U V hV)
    (integralOpenSubtypeVal_isOpenEmbedding V hV)
  change _root_.Topology.IsOpenEmbedding (integralOpenSubtypeVal (U ∩ V))
  exact (hU.inter hV).isOpenEmbedding_subtypeVal

theorem integralOpenSubtypeVal_comp_inclusion
    (U V : Set X) (hU : IsOpen U) :
    (integralOpenSubtypeVal U).comp (integralOpenSubtypeInclusion U V hU) =
      integralOpenSubtypeVal (U ∩ V) := by
  rfl

theorem integralOpenSubtypeVal_comp_inclusionRight
    (U V : Set X) (hV : IsOpen V) :
    (integralOpenSubtypeVal V).comp (integralOpenSubtypeInclusionRight U V hV) =
      integralOpenSubtypeVal (U ∩ V) := by
  rfl

def integralOpenSubtypeUnionInclusion (U V : Set X) (hU : IsOpen U) :
    ContinuousMap U ↥(U ∪ V) :=
  ⟨fun x => ⟨x.1, Or.inl x.2⟩, by
    exact hU.isOpenEmbedding_subtypeVal.continuous.subtype_mk
      (fun x => show (x : X) ∈ U ∪ V from Or.inl x.2)⟩

def integralOpenSubtypeUnionInclusionRight (U V : Set X) (hV : IsOpen V) :
    ContinuousMap V ↥(U ∪ V) :=
  ⟨fun x => ⟨x.1, Or.inr x.2⟩, by
    exact hV.isOpenEmbedding_subtypeVal.continuous.subtype_mk
      (fun x => show (x : X) ∈ U ∪ V from Or.inr x.2)⟩

theorem integralOpenSubtypeUnionInclusion_isOpenEmbedding
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) :
    _root_.Topology.IsOpenEmbedding (integralOpenSubtypeUnionInclusion U V hU) := by
  apply _root_.Topology.IsOpenEmbedding.of_comp
    (integralOpenSubtypeUnionInclusion U V hU)
    ((hU.union hV).isOpenEmbedding_subtypeVal)
  change _root_.Topology.IsOpenEmbedding (integralOpenSubtypeVal U)
  exact hU.isOpenEmbedding_subtypeVal

theorem integralOpenSubtypeUnionInclusionRight_isOpenEmbedding
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) :
    _root_.Topology.IsOpenEmbedding (integralOpenSubtypeUnionInclusionRight U V hV) := by
  apply _root_.Topology.IsOpenEmbedding.of_comp
    (integralOpenSubtypeUnionInclusionRight U V hV)
    ((hU.union hV).isOpenEmbedding_subtypeVal)
  change _root_.Topology.IsOpenEmbedding (integralOpenSubtypeVal V)
  exact hV.isOpenEmbedding_subtypeVal

theorem integralOpenSubtypeVal_union_comp_inclusion
    (U V : Set X) (hU : IsOpen U) :
    (integralOpenSubtypeVal (U ∪ V)).comp
        (integralOpenSubtypeUnionInclusion U V hU) = integralOpenSubtypeVal U := by
  rfl

theorem integralOpenSubtypeVal_union_comp_inclusionRight
    (U V : Set X) (hV : IsOpen V) :
    (integralOpenSubtypeVal (U ∪ V)).comp
        (integralOpenSubtypeUnionInclusionRight U V hV) = integralOpenSubtypeVal V := by
  rfl

def integralCompactSupportOpenDifference
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (q : Nat)
    [T2Space X] :
    integralCompactSupportCohomology ↥(U ∩ V) q ⟶
      integralCompactSupportCohomology U q ⊞ integralCompactSupportCohomology V q :=
  biprod.lift
    (integralCompactSupportCohomologyOpenMap
      (integralOpenSubtypeInclusion U V hU)
      (integralOpenSubtypeInclusion_isOpenEmbedding U V hU hV) q)
    (-integralCompactSupportCohomologyOpenMap
      (integralOpenSubtypeInclusionRight U V hV)
      (integralOpenSubtypeInclusionRight_isOpenEmbedding U V hU hV) q)

def integralCompactSupportOpenSum
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (q : Nat)
    [T2Space X] :
    integralCompactSupportCohomology U q ⊞ integralCompactSupportCohomology V q ⟶
      integralCompactSupportCohomology ↥(U ∪ V) q :=
  biprod.desc
    (integralCompactSupportCohomologyOpenMap
      (integralOpenSubtypeUnionInclusion U V hU)
      (integralOpenSubtypeUnionInclusion_isOpenEmbedding U V hU hV) q)
    (integralCompactSupportCohomologyOpenMap
      (integralOpenSubtypeUnionInclusionRight U V hV)
      (integralOpenSubtypeUnionInclusionRight_isOpenEmbedding U V hU hV) q)

@[reassoc (attr := simp)]
theorem integralCompactSupportOpenDifference_sum
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (q : Nat)
    [T2Space X] :
    integralCompactSupportOpenDifference U V hU hV q ≫
      integralCompactSupportOpenSum U V hU hV q = 0 := by
  rw [integralCompactSupportOpenDifference, integralCompactSupportOpenSum,
    biprod.lift_desc, Preadditive.neg_comp]
  rw [integralCompactSupportCohomologyOpenMap_comp,
    integralCompactSupportCohomologyOpenMap_comp]
  have hmaps :
      (integralOpenSubtypeUnionInclusion U V hU).comp
          (integralOpenSubtypeInclusion U V hU) =
        (integralOpenSubtypeUnionInclusionRight U V hV).comp
          (integralOpenSubtypeInclusionRight U V hV) := by
    ext x
    rfl
  let hu := (integralOpenSubtypeUnionInclusion_isOpenEmbedding U V hU hV).comp
    (integralOpenSubtypeInclusion_isOpenEmbedding U V hU hV)
  let hv := (integralOpenSubtypeUnionInclusionRight_isOpenEmbedding U V hU hV).comp
    (integralOpenSubtypeInclusionRight_isOpenEmbedding U V hU hV)
  have hmap :
      integralCompactSupportCohomologyOpenMap
          ((integralOpenSubtypeUnionInclusion U V hU).comp
            (integralOpenSubtypeInclusion U V hU)) hu q =
        integralCompactSupportCohomologyOpenMap
          ((integralOpenSubtypeUnionInclusionRight U V hV).comp
            (integralOpenSubtypeInclusionRight U V hV)) hv q := by
    cases hmaps
    rfl
  simpa only [hu, hv] using (hmap ▸ add_neg_cancel
    (integralCompactSupportCohomologyOpenMap
      ((integralOpenSubtypeUnionInclusionRight U V hV).comp
        (integralOpenSubtypeInclusionRight U V hV)) hv q))

end PoincareConjecture.Proofs.M02.Topology
