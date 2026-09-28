import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSupportImageTransport
import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSubtype









set_option autoImplicit false

noncomputable section

open CategoryTheory Limits TopologicalSpace Set

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable {X : Type u} [TopologicalSpace X] [T2Space X]

theorem integralCompactSupportOpenMayerVietoris_tail
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (q : Nat)
    (A : Compacts U) (B : Compacts V)
    (R : Compacts ↥(U ∪ V))
    (hRA : (R : Set ↥(U ∪ V)) ⊆
      (integralOpenSubtypeUnionInclusion U V hU) '' (A : Set U))
    (hRB : (R : Set ↥(U ∪ V)) ⊆
      (integralOpenSubtypeUnionInclusionRight U V hV) '' (B : Set V))
    (c : integralSupportCohomology (R : Set ↥(U ∪ V)) q) :
    ∃ z : integralCompactSupportCohomology ↥(U ∩ V) q,
      integralCompactSupportCohomologyOpenMap
          (integralOpenSubtypeInclusion U V hU)
          (integralOpenSubtypeInclusion_isOpenEmbedding U V hU hV) q z =
        integralCompactSupportCohomologyClass A q
          ((integralSupportOpenEmbeddingCohomologyIso
            (integralOpenSubtypeUnionInclusion U V hU)
            (integralOpenSubtypeUnionInclusion_isOpenEmbedding U V hU hV) A q).hom
            (integralSupportCohomologyPushforward hRA q c)) ∧
      integralCompactSupportCohomologyOpenMap
          (integralOpenSubtypeInclusionRight U V hV)
          (integralOpenSubtypeInclusionRight_isOpenEmbedding U V hU hV) q z =
        integralCompactSupportCohomologyClass B q
          ((integralSupportOpenEmbeddingCohomologyIso
            (integralOpenSubtypeUnionInclusionRight U V hV)
            (integralOpenSubtypeUnionInclusionRight_isOpenEmbedding U V hU hV) B q).hom
            (integralSupportCohomologyPushforward hRB q c)) := by
  let fU := integralOpenSubtypeUnionInclusion U V hU
  let fV := integralOpenSubtypeUnionInclusionRight U V hV
  let iU := integralOpenSubtypeInclusion U V hU
  let iV := integralOpenSubtypeInclusionRight U V hV
  let hfU := integralOpenSubtypeUnionInclusion_isOpenEmbedding U V hU hV
  let hfV := integralOpenSubtypeUnionInclusionRight_isOpenEmbedding U V hU hV
  let hiU := integralOpenSubtypeInclusion_isOpenEmbedding U V hU hV
  let hiV := integralOpenSubtypeInclusionRight_isOpenEmbedding U V hU hV
  let t := fU.comp iU
  have ht : _root_.Topology.IsOpenEmbedding t := hfU.comp hiU
  have htV : t = fV.comp iV := by
    ext x
    rfl
  have hR : (R : Set ↥(U ∪ V)) ⊆ Set.range t := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := hRA hx
    obtain ⟨b, hb, hbx⟩ := hRB hx
    have hUx : (x : X) ∈ U := congrArg Subtype.val hax ▸ a.property
    have hVx : (x : X) ∈ V := congrArg Subtype.val hbx ▸ b.property
    exact ⟨⟨x, hUx, hVx⟩, Subtype.ext rfl⟩
  obtain ⟨S, hSR⟩ := exists_integralCompact_preimage_of_subset_range t ht R hR
  have hRS : (R : Set ↥(U ∪ V)) ⊆ t '' (S : Set ↥(U ∩ V)) := by
    intro x hx
    change x ∈ (S.map t t.continuous : Set ↥(U ∪ V))
    rw [hSR]
    exact hx
  refine ⟨integralCompactSupportCohomologyClass S q
    ((integralSupportOpenEmbeddingCohomologyIso t ht S q).hom
      (integralSupportCohomologyPushforward hRS q c)), ?_, ?_⟩
  · exact integralCompactSupportCohomologyOpenMap_class_of_composite_support
      iU fU t hiU hfU ht rfl S R A hSR hRS hRA q c
  · exact integralCompactSupportCohomologyOpenMap_class_of_composite_support
      iV fV t hiV hfV ht htV S R B hSR hRS hRB q c

end PoincareConjecture.Proofs.M02.Topology
