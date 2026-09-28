import PoincareConjecture.Proofs.M38.CappingInclusions
import PoincareConjecture.Proofs.M38.CappingRemainder








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38



theorem capInnerBall_compact :
    IsCompact {x : capDoubleBall | ‖x.val‖ ≤ (3 / 2 : ℝ)} := by
  apply IsEmbedding.subtypeVal.isCompact_iff.mpr
  have heq : Subtype.val '' {x : capDoubleBall | ‖x.val‖ ≤ (3 / 2 : ℝ)} =
      Metric.closedBall (0 : StandardCapSpace) (3 / 2) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      change ‖z.val‖ ≤ (3 / 2 : ℝ) at hz
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    · intro hx
      have hnorm : ‖x‖ ≤ (3 / 2 : ℝ) := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hx
      exact ⟨⟨x, by change dist x 0 < 2; rw [dist_zero_right]; linarith⟩, hnorm, rfl⟩
  rw [heq]
  exact isCompact_closedBall _ _

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)



theorem cappedOldInclusion_cap (i : Fin (F.event T hT).cap_count) (x : capDoubleBall)
    (hx : 1 < ‖x.val‖) :
    cappedOldInclusion F T hT P ((P i).attachmentChart x) =
      eventCappingInclude F T hT P (.inr i) x := by
  let y := (P i).attachmentChart x
  let z : eventCappingDomain F T hT (.inl y) :=
    ⟨chartAt StandardCapSpace y y,
      (chartAt StandardCapSpace y).map_source (mem_chart_source _ y)⟩
  have hz := cappedOldInclusion_patch F T hT P y z
  rw [show eventCappingMap F T hT P (.inl y) z = y from
    eventCappingMap_old_center F T hT P y] at hz
  apply hz.trans
  apply (cappingOverlap_include_iff_image (eventCappingMap F T hT P)
    (i := .inl y) (j := .inr i)
    (by rw [eventCappingMap_old_source]; exact Set.mem_univ _)
    (by change x ∈ (P i).attachmentChart.source; rwa [(P i).attachmentChart_source])).mpr
  exact eventCappingMap_old_center F T hT P y


theorem cappingOldRemainder_compact :
    IsCompact ((Subtype.val : eventDiscardedOpen F T hT →
      (F.slice (F.event T hT).tMinus).carrier) ⁻¹' eventCappingRemainder F T hT P) := by
  apply IsEmbedding.subtypeVal.isInducing.isCompact_preimage'
    (eventCappingRemainder_compact F T hT P)
  intro x hx
  exact ⟨⟨x, eventCappingRemainder_discarded F T hT P hx⟩, rfl⟩



theorem cappedOldInclusion_compact_cover (y : eventDiscardedOpen F T hT) :
    cappedOldInclusion F T hT P y ∈
      cappedOldInclusion F T hT P '' (Subtype.val ⁻¹' eventCappingRemainder F T hT P) ∪
        ⋃ i, eventCappingInclude F T hT P (.inr i) ''
          {x : capDoubleBall | ‖x.val‖ ≤ (3 / 2 : ℝ)} := by
  by_cases hy : y.val ∈ eventCappingRemainder F T hT P
  · exact Or.inl ⟨y, hy, rfl⟩
  obtain ⟨i, z, s, hs, hmap⟩ := eventCappingRemainder_cover F T hT P y.property hy
  have hz : (z, s) ∈ Set.univ ×ˢ Set.Ioo (0 : ℝ) 1 :=
    ⟨Set.mem_univ _, hs.1, by linarith [hs.2]⟩
  have hnorm : ‖capAttachVector (z, s)‖ = 1 + s := by
    simp [capAttachVector, norm_smul, abs_of_pos (by linarith [hs.1] : 0 < 1 + s)]
  let x : capDoubleBall := ⟨capAttachVector (z, s), by
    change dist (capAttachVector (z, s)) 0 < 2
    rw [dist_zero_right, hnorm]
    linarith [hs.2]⟩
  have hx : 1 < ‖x.val‖ := by dsimp [x]; rw [hnorm]; linarith [hs.1]
  have hattach : (P i).attachmentChart x = y := by
    apply Subtype.ext
    rw [(P i).attachmentChart_apply hx]
    change (P i).collar (capAttachCoordinates (capAttachVector (z, s))) = y.val
    rw [capAttachCoordinates_vector hz]
    exact hmap
  apply Or.inr
  refine Set.mem_iUnion.mpr ⟨i, x, ?_, ?_⟩
  · change ‖capAttachVector (z, s)‖ ≤ 3 / 2
    rw [hnorm]
    linarith [hs.2]
  · rw [← cappedOldInclusion_cap F T hT P i x hx, hattach]



theorem cappedDiscardedSpace_compact_cover :
    cappedOldInclusion F T hT P '' (Subtype.val ⁻¹' eventCappingRemainder F T hT P) ∪
        (⋃ i, eventCappingInclude F T hT P (.inr i) ''
          {x : capDoubleBall | ‖x.val‖ ≤ (3 / 2 : ℝ)}) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  induction q using Quotient.inductionOn with
  | h a =>
      rcases a with ⟨j, x⟩
      cases j with
      | inl y =>
          have h := cappedOldInclusion_compact_cover F T hT P
            (eventCappingMap F T hT P (.inl y) x)
          rw [cappedOldInclusion_patch] at h
          exact h
      | inr i =>
          by_cases hx : ‖x.val‖ ≤ (3 / 2 : ℝ)
          · exact Or.inr (Set.mem_iUnion.mpr ⟨i, x, hx, rfl⟩)
          · have hpos : 1 < ‖x.val‖ := by linarith [lt_of_not_ge hx]
            have h := cappedOldInclusion_compact_cover F T hT P ((P i).attachmentChart x)
            rw [cappedOldInclusion_cap F T hT P i x hpos] at h
            exact h



theorem cappedDiscardedSpace_compact : CompactSpace (CappedDiscardedSpace F T hT P) := by
  apply isCompact_univ_iff.mp
  rw [← cappedDiscardedSpace_compact_cover F T hT P]
  exact ((cappingOldRemainder_compact F T hT P).image
    (cappedOldInclusion_openEmbedding F T hT P).continuous).union
      (isCompact_iUnion fun i => capInnerBall_compact.image
        (eventCappingInclude_openEmbedding F T hT P (.inr i)).continuous)

end PoincareConjecture.M38
