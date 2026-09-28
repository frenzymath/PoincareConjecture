import PoincareConjecture.Proofs.M38.FullCutOverlap
import PoincareConjecture.Proofs.M38.RetainedComponents









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)


theorem retained_subset_fullCut :
    eventRetainedInteriorOpen F T hT ≤ eventCutOpen F T hT P Set.univ := by
  intro x hx
  change x ∈ (eventCutOpen F T hT P Set.univ : Set _)
  rw [eventCutOpen_univ]
  exact Or.inl hx


theorem discarded_subset_fullCut :
    eventDiscardedOpen F T hT ≤ eventCutOpen F T hT P Set.univ := by
  intro x hx
  change x ∈ (eventCutOpen F T hT P Set.univ : Set _)
  rw [eventCutOpen_univ]
  exact Or.inr hx


noncomputable def fullCutRetained :
    eventRetainedInteriorOpen F T hT → eventCutOpen F T hT P Set.univ :=
  Set.inclusion (retained_subset_fullCut F T hT P)


noncomputable def fullCutDiscarded :
    eventDiscardedOpen F T hT → eventCutOpen F T hT P Set.univ :=
  Set.inclusion (discarded_subset_fullCut F T hT P)


theorem fullCutRetained_openEmbedding : IsOpenEmbedding (fullCutRetained F T hT P) :=
  .inclusion (retained_subset_fullCut F T hT P)
    ((eventRetainedInteriorOpen F T hT).isOpen.preimage continuous_subtype_val)


theorem fullCutDiscarded_openEmbedding : IsOpenEmbedding (fullCutDiscarded F T hT P) :=
  .inclusion (discarded_subset_fullCut F T hT P)
    ((eventDiscardedOpen F T hT).isOpen.preimage continuous_subtype_val)


theorem fullCutRetained_smooth : ContMDiff (𝓡 3) (𝓡 3) ∞ (fullCutRetained F T hT P) :=
  contMDiff_inclusion (retained_subset_fullCut F T hT P)


theorem fullCutDiscarded_smooth : ContMDiff (𝓡 3) (𝓡 3) ∞ (fullCutDiscarded F T hT P) :=
  contMDiff_inclusion (discarded_subset_fullCut F T hT P)


noncomputable def fullCutPostOld :
    eventCapComplementOpen F T hT → eventCutOpen F T hT P Set.univ :=
  fullCutRetained F T hT P ∘ (retentionInteriorHomeomorph F T hT).symm


theorem fullCutPostOld_openEmbedding : IsOpenEmbedding (fullCutPostOld F T hT P) :=
  (fullCutRetained_openEmbedding F T hT P).comp
    (retentionInteriorHomeomorph F T hT).symm.isOpenEmbedding


theorem fullCut_old_sides_disjoint :
    Disjoint (Set.range (fullCutPostOld F T hT P))
      (Set.range (fullCutDiscarded F T hT P)) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨y, rfl⟩ ⟨z, hz⟩
  have heq := congrArg Subtype.val hz
  exact z.property (heq.symm ▸ interior_subset
    ((retentionInteriorHomeomorph F T hT).symm y).property)


theorem fullCut_old_cover :
    Set.range (fullCutPostOld F T hT P) ∪ Set.range (fullCutDiscarded F T hT P) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx := x.property
  change x.val ∈ (eventCutOpen F T hT P Set.univ : Set _) at hx
  rw [eventCutOpen_univ] at hx
  rcases hx with hr | hd
  · left
    refine ⟨retentionInteriorHomeomorph F T hT ⟨x.val, hr⟩, ?_⟩
    dsimp [fullCutPostOld]
    rw [Homeomorph.symm_apply_apply]
    exact Subtype.ext rfl
  · exact Or.inr ⟨⟨x.val, hd⟩, Subtype.ext rfl⟩


theorem fullCut_positive_attachment (i : Fin (F.event T hT).cap_count)
    (x : capDoubleBall) (hx : 1 < ‖x.val‖) :
    cutAttachmentChart F T hT P Set.univ (⟨i, Set.mem_univ i⟩, true) x =
      fullCutDiscarded F T hT P ((P i).attachmentChart x) := by
  apply Subtype.ext
  rw [cutAttachmentChart_apply F T hT P Set.univ _ hx]
  change (P i).collar (cutSideReflection true (capAttachCoordinates x.val)) =
    ((P i).attachmentChart x).val
  rw [(P i).attachmentChart_apply hx]
  rfl


theorem fullCut_negative_attachment (i : Fin (F.event T hT).cap_count)
    (x : capDoubleBall) (hx : 1 < ‖x.val‖) :
    cutAttachmentChart F T hT P Set.univ (⟨i, Set.mem_univ i⟩, false) x =
      fullCutPostOld F T hT P
        ⟨(P i).ball.map x.val, ((P i).ball_mem_cap_complement_iff x.property).mpr hx⟩ := by
  apply Subtype.ext
  rw [cutAttachmentChart_apply F T hT P Set.univ _ hx]
  have hn : ‖x.val‖ < 2 := by
    simpa only [capDoubleBall, TopologicalSpace.Opens.mem_mk, Metric.mem_ball,
      dist_zero_right] using x.property
  have hs : 1 - ‖x.val‖ ∈ Set.Ioo (-1 : ℝ) 0 := by constructor <;> linarith
  have h := (P i).negative_gluing (capUnitDirection x.val) (1 - ‖x.val‖) hs
  rw [show 1 - (1 - ‖x.val‖) = ‖x.val‖ by ring, capUnitDirection_radial] at h
  change (P i).collar (cutSideReflection false (capAttachCoordinates x.val)) =
    (F.event T hT).retention.inverse ((P i).ball.map x.val)
  rw [cutSideReflection_apply]
  dsimp [capAttachCoordinates]
  simpa only [neg_sub] using h

end PoincareConjecture.M38
