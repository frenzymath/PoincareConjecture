import PoincareLib.Topology.Manifold.Surgery.Event.Partial.PartialCutDomains
import PoincareLib.Topology.Manifold.Surgery.Event.Capping.CappingPatchSmooth

/-!
# Actual attaching patches for a selected family of cuts

Each selected sphere has two ball patches. Their outer annuli map to
the indicated actual collar sides in the same open pre-slice domain.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
  (S : Set (Fin (F.event T hT).cap_count))

/-- The actual reflected annulus restricted to the two open patch types. -/
noncomputable def cutAttachmentChart (a : S × Bool) :
    OpenPartialHomeomorph capDoubleBall (eventCutOpen F T hT P S) :=
  ((((P a.1.val).cutAnnularChart a.2).subtypeRestr capDoubleBall_nonempty).symm.subtypeRestr
    (eventCutOpen_nonempty F T hT P S a.1.val a.2)).symm

/-- The source is exactly the outer annulus inside the open radius-two ball. -/
theorem cutAttachmentChart_source (a : S × Bool) :
    (cutAttachmentChart F T hT P S a).source = {x : capDoubleBall | 1 < ‖x.val‖} := by
  rw [cutAttachmentChart, partialSubtype_both_source _ _ _ _ _
    (cutAnnularChart_target_cutOpen F T hT P S a.1.val a.2)]
  ext x
  change (1 < ‖x.val‖ ∧ ‖x.val‖ < 2) ↔ 1 < ‖x.val‖
  exact and_iff_left (by simpa only [capDoubleBall, TopologicalSpace.Opens.mem_mk,
    Metric.mem_ball, dist_zero_right] using x.property)

/-- The target keeps exactly the specified actual half-collar image. -/
theorem cutAttachmentChart_target (a : S × Bool) :
    (cutAttachmentChart F T hT P S a).target =
      Subtype.val ⁻¹' ((P a.1.val).cutAnnularChart a.2).target := by
  change ((((P a.1.val).cutAnnularChart a.2).subtypeRestr capDoubleBall_nonempty).symm.subtypeRestr
    (eventCutOpen_nonempty F T hT P S a.1.val a.2)).source = _
  rw [OpenPartialHomeomorph.subtypeRestr_source, OpenPartialHomeomorph.symm_source]
  rw [partialSubtype_target ((P a.1.val).cutAnnularChart a.2)
    capDoubleBall capDoubleBall_nonempty]
  intro x hx
  exact Metric.mem_ball.mpr (by simpa only [dist_zero_right] using hx.2)

/-- The restricted point map is still the same literal reflected collar formula. -/
theorem cutAttachmentChart_apply (a : S × Bool) {x : capDoubleBall} (hx : 1 < ‖x.val‖) :
    (cutAttachmentChart F T hT P S a x).val =
      (P a.1.val).collar (cutSideReflection a.2 (capAttachCoordinates x.val)) := by
  have hsrc : x ∈ (cutAttachmentChart F T hT P S a).source := by
    rwa [cutAttachmentChart_source]
  exact (((P a.1.val).cutAnnularChart a.2).subtypeRestr
    capDoubleBall_nonempty).symm.subtypeRestr_symm_apply
      (eventCutOpen_nonempty F T hT P S a.1.val a.2) hsrc

/-- The restricted inverse has the same reflected radial vector formula. -/
theorem cutAttachmentChart_symm_apply (a : S × Bool) {y : eventCutOpen F T hT P S}
    (hy : y ∈ (cutAttachmentChart F T hT P S a).target) :
    ((cutAttachmentChart F T hT P S a).symm y).val =
      capAttachVector (cutSideReflection a.2 ((P a.1.val).collarInverse y.val)) := by
  change ((((P a.1.val).cutAnnularChart a.2).subtypeRestr
    capDoubleBall_nonempty).symm y.val).val = _
  simp only [cutAttachmentChart, OpenPartialHomeomorph.symm_target,
    OpenPartialHomeomorph.subtypeRestr_source, OpenPartialHomeomorph.symm_source,
    Set.mem_preimage] at hy
  exact ((P a.1.val).cutAnnularChart a.2).subtypeRestr_symm_apply capDoubleBall_nonempty hy

/-- The inner annular limit is on a removed selected sphere, so the graph is closed. -/
theorem cutAttachmentChart_graph_closed (a : S × Bool) :
    IsClosed {q : capDoubleBall × eventCutOpen F T hT P S |
      q.1 ∈ (cutAttachmentChart F T hT P S a).source ∧
        cutAttachmentChart F T hT P S a q.1 = q.2} := by
  have hC : ContinuousOn ((P a.1.val).collar ∘ cutSideReflection a.2)
      (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) :=
    ((event_cap_collar_smooth F T hT a.1.val (P a.1.val).width_pos
      (P a.1.val).width_lt (P a.1.val).shell_domain).comp
      (cutSideReflection a.2).contMDiff.contMDiffOn
      (fun z hz => (cutSideReflection_mem_full a.2 z).mpr hz)).continuousOn
  have hc (z : UnitTwoSphere) :
      ((P a.1.val).collar ∘ cutSideReflection a.2) (z, 0) ∈ eventCutSpheres F T hT P S := by
    rw [Function.comp_apply, cutSideReflection_zero]
    exact Set.mem_iUnion.mpr ⟨a.1, (z, 0), by simp, rfl⟩
  have h := cap_attachment_graph_closed _ hC hc
  have heq : {q : capDoubleBall × eventCutOpen F T hT P S |
      q.1 ∈ (cutAttachmentChart F T hT P S a).source ∧
        cutAttachmentChart F T hT P S a q.1 = q.2} =
      {q : capDoubleBall × eventCutOpen F T hT P S |
        1 < ‖q.1.val‖ ∧ (P a.1.val).collar
          (cutSideReflection a.2 (capAttachCoordinates q.1.val)) = q.2.val} := by
    ext q
    rw [Set.mem_setOf_eq, cutAttachmentChart_source]
    change (1 < ‖q.1.val‖ ∧ cutAttachmentChart F T hT P S a q.1 = q.2) ↔ _
    constructor
    · rintro ⟨hx, hxy⟩
      exact ⟨hx, (cutAttachmentChart_apply F T hT P S a hx).symm.trans
        (congrArg Subtype.val hxy)⟩
    · rintro ⟨hx, hxy⟩
      exact ⟨hx, Subtype.ext ((cutAttachmentChart_apply F T hT P S a hx).trans hxy)⟩
  rw [heq]
  exact h

/-- All distinct selected side patches attach to disjoint parts of the old domain. -/
theorem cutAttachmentChart_targets_disjoint (a b : S × Bool) (hab : a ≠ b) :
    Disjoint (cutAttachmentChart F T hT P S a).target
      (cutAttachmentChart F T hT P S b).target := by
  rw [cutAttachmentChart_target, cutAttachmentChart_target]
  exact (cutAnnularChart_targets_disjoint F T hT P S a b hab).preimage Subtype.val

/-- Both actual maps are smooth in the singleton ball chart and inherited old atlas. -/
theorem cutAttachmentChart_smooth (a : S × Bool) :
    letI : Nonempty capDoubleBall := capDoubleBall_nonempty
    letI := capDoubleBall.isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (cutAttachmentChart F T hT P S a)
        (cutAttachmentChart F T hT P S a).source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ (cutAttachmentChart F T hT P S a).symm
        (cutAttachmentChart F T hT P S a).target := by
  letI : Nonempty capDoubleBall := capDoubleBall_nonempty
  letI := capDoubleBall.isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
  constructor
  · have hdom : Set.MapsTo (Subtype.val : capDoubleBall → StandardCapSpace)
        (cutAttachmentChart F T hT P S a).source ((P a.1.val).cutAnnularChart a.2).source := by
      intro x hx
      rw [cutAttachmentChart_source] at hx
      exact ⟨hx, by simpa only [capDoubleBall, TopologicalSpace.Opens.mem_mk,
        Metric.mem_ball, dist_zero_right] using x.property⟩
    have hs := ((P a.1.val).cutAnnular_map_smooth a.2).comp
      (contMDiff_isOpenEmbedding (I := 𝓡 3) (n := ∞)
        capDoubleBall.isOpen.isOpenEmbedding_subtypeVal).contMDiffOn hdom
    have hcoe : ContMDiffOn (𝓡 3) (𝓡 3) ∞
        (Subtype.val ∘ cutAttachmentChart F T hT P S a)
        (cutAttachmentChart F T hT P S a).source :=
      hs.congr (fun x hx => cutAttachmentChart_apply F T hT P S a
        (by rwa [cutAttachmentChart_source] at hx))
    intro x hx
    exact (ContMDiffWithinAt.subtypeVal_comp_iff (eventCutOpen F T hT P S)
      (cutAttachmentChart F T hT P S a) (cutAttachmentChart F T hT P S a).source x).mp
        (hcoe x hx)
  · have hdom : Set.MapsTo
        (Subtype.val : eventCutOpen F T hT P S → (F.slice (F.event T hT).tMinus).carrier)
        (cutAttachmentChart F T hT P S a).target ((P a.1.val).cutAnnularChart a.2).target := by
      intro y hy
      rwa [cutAttachmentChart_target] at hy
    have hs := ((P a.1.val).cutAnnular_inverse_smooth a.2).comp
      contMDiff_subtype_val.contMDiffOn hdom
    have hrange (y : eventCutOpen F T hT P S)
        (hy : y ∈ (cutAttachmentChart F T hT P S a).target) :
        capAttachVector (cutSideReflection a.2 ((P a.1.val).collarInverse y.val)) ∈
          Set.range (Subtype.val : capDoubleBall → StandardCapSpace) :=
      ⟨(cutAttachmentChart F T hT P S a).symm y,
        cutAttachmentChart_symm_apply F T hT P S a hy⟩
    have hcomp := (contMDiffOn_isOpenEmbedding_symm (I := 𝓡 3) (n := ∞)
      capDoubleBall.isOpen.isOpenEmbedding_subtypeVal).comp hs hrange
    apply hcomp.congr
    intro y hy
    apply Subtype.ext
    exact (cutAttachmentChart_symm_apply F T hT P S a hy).trans
      (Topology.IsOpenEmbedding.toOpenPartialHomeomorph_right_inv
        (f := (Subtype.val : capDoubleBall → StandardCapSpace))
        (h := capDoubleBall.isOpen.isOpenEmbedding_subtypeVal) (hrange y hy)).symm

end PoincareMT.M38
