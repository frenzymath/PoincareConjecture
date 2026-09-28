import PoincareConjecture.Proofs.M38.PartialCutInclusions
import PoincareConjecture.Proofs.M38.CappingCompact








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
  (S : Set (Fin (F.event T hT).cap_count))


theorem partialOldRemainder_compact :
    IsCompact ((Subtype.val : eventCutOpen F T hT P S →
      (F.slice (F.event T hT).tMinus).carrier) ⁻¹' eventCutRemainder F T hT P S) := by
  apply IsEmbedding.subtypeVal.isInducing.isCompact_preimage'
    (eventCutRemainder_compact F T hT P S)
  intro x hx
  exact ⟨⟨x, eventCutRemainder_subset F T hT P S hx⟩, rfl⟩


theorem partialOldInclusion_compact_cover (y : eventCutOpen F T hT P S) :
    partialOldInclusion F T hT P S y ∈
      partialOldInclusion F T hT P S '' (Subtype.val ⁻¹' eventCutRemainder F T hT P S) ∪
        ⋃ a : S × Bool, partialCappingInclude F T hT P S (.inr a) ''
          {x : capDoubleBall | ‖x.val‖ ≤ (3 / 2 : ℝ)} := by
  by_cases hy : y.val ∈ eventCutRemainder F T hT P S
  · exact Or.inl ⟨y, hy, rfl⟩
  obtain ⟨i, positive, z, s, hs, hmap⟩ :=
    eventCutRemainder_cover F T hT P S y.property hy
  have hz : (z, s) ∈ Set.univ ×ˢ Set.Ioo (0 : ℝ) 1 :=
    ⟨Set.mem_univ _, hs.1, by linarith [hs.2]⟩
  have hnorm : ‖capAttachVector (z, s)‖ = 1 + s := by
    simp [capAttachVector, norm_smul, abs_of_pos (by linarith [hs.1] : 0 < 1 + s)]
  let x : capDoubleBall := ⟨capAttachVector (z, s), by
    change dist (capAttachVector (z, s)) 0 < 2
    rw [dist_zero_right, hnorm]
    linarith [hs.2]⟩
  have hx : 1 < ‖x.val‖ := by dsimp [x]; rw [hnorm]; linarith [hs.1]
  have hattach : cutAttachmentChart F T hT P S (i, positive) x = y := by
    apply Subtype.ext
    rw [cutAttachmentChart_apply F T hT P S (i, positive) hx]
    change (P i.val).collar
      (cutSideReflection positive (capAttachCoordinates (capAttachVector (z, s)))) = y.val
    rw [capAttachCoordinates_vector hz]
    exact hmap
  apply Or.inr
  refine Set.mem_iUnion.mpr ⟨(i, positive), x, ?_, ?_⟩
  · change ‖capAttachVector (z, s)‖ ≤ 3 / 2
    rw [hnorm]
    linarith [hs.2]
  · rw [← partialOldInclusion_cap F T hT P S (i, positive) x hx, hattach]


theorem partialCappedSpace_compact_cover :
    partialOldInclusion F T hT P S '' (Subtype.val ⁻¹' eventCutRemainder F T hT P S) ∪
        (⋃ a : S × Bool, partialCappingInclude F T hT P S (.inr a) ''
          {x : capDoubleBall | ‖x.val‖ ≤ (3 / 2 : ℝ)}) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  induction q using Quotient.inductionOn with
  | h a =>
      rcases a with ⟨j, x⟩
      cases j with
      | inl y =>
          have h := partialOldInclusion_compact_cover F T hT P S
            (partialCappingMap F T hT P S (.inl y) x)
          rw [partialOldInclusion_patch] at h
          exact h
      | inr a =>
          by_cases hx : ‖x.val‖ ≤ (3 / 2 : ℝ)
          · exact Or.inr (Set.mem_iUnion.mpr ⟨a, x, hx, rfl⟩)
          · have hpos : 1 < ‖x.val‖ := by linarith [lt_of_not_ge hx]
            have h := partialOldInclusion_compact_cover F T hT P S
              (cutAttachmentChart F T hT P S a x)
            rw [partialOldInclusion_cap F T hT P S a x hpos] at h
            exact h


theorem partialCappedSpace_compact : CompactSpace (PartialCappedSpace F T hT P S) := by
  apply isCompact_univ_iff.mp
  rw [← partialCappedSpace_compact_cover F T hT P S]
  exact ((partialOldRemainder_compact F T hT P S).image
    (partialOldInclusion_openEmbedding F T hT P S).continuous).union
      (isCompact_iUnion fun a => capInnerBall_compact.image
        (partialCappingInclude_openEmbedding F T hT P S (.inr a)).continuous)


noncomputable def partialCappedCarrier : GeneralizedSliceCarrier.{u} := by
  letI := partialCappedChartedSpace F T hT P S
  letI := partialCappedSpace_isManifold F T hT P S
  letI := partialCappedSpace_t2 F T hT P S
  letI := partialCappedSpace_compact F T hT P S
  letI : MeasurableSpace (PartialCappedSpace F T hT P S) :=
    borel (PartialCappedSpace F T hT P S)
  exact {
    carrier := PartialCappedSpace F T hT P S
    topologicalSpace := inferInstance
    measurableSpace := inferInstance
    borelSpace := ⟨rfl⟩
    chartedSpace := partialCappedChartedSpace F T hT P S
    isManifold := inferInstance
    t2Space := inferInstance
    t3Space := inferInstance
    secondCountable := ChartedSpace.secondCountable_of_sigmaCompact StandardCapSpace _ }


theorem partialCappedCarrier_compact :
    IsCompact (Set.univ : Set (partialCappedCarrier F T hT P S).carrier) := by
  change IsCompact (Set.univ : Set (PartialCappedSpace F T hT P S))
  letI := partialCappedSpace_compact F T hT P S
  exact isCompact_univ

end PoincareConjecture.M38
