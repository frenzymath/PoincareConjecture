import PoincareConjecture.Proofs.M38.CapAnnulus
import PoincareConjecture.Proofs.M38.PartialChartRestriction









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M38


def capDoubleBall : TopologicalSpace.Opens StandardCapSpace :=
  ⟨Metric.ball 0 2, Metric.isOpen_ball⟩


theorem capDoubleBall_nonempty : Nonempty capDoubleBall :=
  ⟨⟨0, by simp [capDoubleBall]⟩⟩

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier]



def eventDiscardedOpen :
    TopologicalSpace.Opens (F.slice (F.event T hT).tMinus).carrier :=
  ⟨(F.event T hT).retained_preᶜ, (F.event T hT).retained_pre_compact.isClosed.isOpen_compl⟩

namespace EventCapCoordinates

variable {F T hT} {i : Fin (F.event T hT).cap_count}
  (P : EventCapCoordinates F T hT i)

include P in

theorem discarded_nonempty : Nonempty (eventDiscardedOpen F T hT) := by
  refine ⟨⟨P.collar (capUnitDirection 0, 1 / 2), ?_⟩⟩
  exact P.annular_target_discarded
    ⟨(capUnitDirection 0, 1 / 2), ⟨Set.mem_univ _, by norm_num⟩, rfl⟩



noncomputable def attachmentChart :
    OpenPartialHomeomorph capDoubleBall (eventDiscardedOpen F T hT) :=
  ((P.annularChart.subtypeRestr capDoubleBall_nonempty).symm.subtypeRestr
    P.discarded_nonempty).symm


theorem attachmentChart_source :
    P.attachmentChart.source = {x : capDoubleBall | 1 < ‖x.val‖} := by
  rw [attachmentChart, partialSubtype_both_source _ _ _ _ _
    P.annular_target_discarded]
  ext x
  change (1 < ‖x.val‖ ∧ ‖x.val‖ < 2) ↔ 1 < ‖x.val‖
  exact and_iff_left (by simpa only [capDoubleBall, TopologicalSpace.Opens.mem_mk,
    Metric.mem_ball, dist_zero_right] using x.property)


theorem attachmentChart_target :
    P.attachmentChart.target =
      Subtype.val ⁻¹' (P.collar '' (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1)) := by
  change ((P.annularChart.subtypeRestr capDoubleBall_nonempty).symm.subtypeRestr
    P.discarded_nonempty).source = _
  rw [OpenPartialHomeomorph.subtypeRestr_source, OpenPartialHomeomorph.symm_source]
  rw [partialSubtype_target P.annularChart capDoubleBall capDoubleBall_nonempty]
  · rfl
  · intro x hx
    exact (Metric.mem_ball.mpr (by simpa only [dist_zero_right] using hx.2))



theorem attachmentChart_apply {x : capDoubleBall} (hx : 1 < ‖x.val‖) :
    (P.attachmentChart x).val = P.collar (capAttachCoordinates x.val) := by
  have hsrc : x ∈ P.attachmentChart.source := by rwa [P.attachmentChart_source]
  exact (P.annularChart.subtypeRestr capDoubleBall_nonempty).symm.subtypeRestr_symm_apply
    P.discarded_nonempty hsrc



theorem attachmentChart_graph_closed :
    IsClosed {q : capDoubleBall × eventDiscardedOpen F T hT |
      q.1 ∈ P.attachmentChart.source ∧ P.attachmentChart q.1 = q.2} := by
  have heq : {q : capDoubleBall × eventDiscardedOpen F T hT |
      q.1 ∈ P.attachmentChart.source ∧ P.attachmentChart q.1 = q.2} =
        {q : capDoubleBall × eventDiscardedOpen F T hT |
          1 < ‖q.1.val‖ ∧ P.collar (capAttachCoordinates q.1.val) = q.2.val} := by
    ext q
    rw [Set.mem_setOf_eq, P.attachmentChart_source]
    change (1 < ‖q.1.val‖ ∧ P.attachmentChart q.1 = q.2) ↔ _
    constructor
    · rintro ⟨hx, hxy⟩
      exact ⟨hx, (P.attachmentChart_apply hx).symm.trans (congrArg Subtype.val hxy)⟩
    · rintro ⟨hx, hxy⟩
      exact ⟨hx, Subtype.ext ((P.attachmentChart_apply hx).trans hxy)⟩
  rw [heq]
  exact P.attachment_graph_closed


theorem attachmentChart_targets_disjoint {j : Fin (F.event T hT).cap_count}
    (Q : EventCapCoordinates F T hT j) (hij : i ≠ j) :
    Disjoint P.attachmentChart.target Q.attachmentChart.target := by
  rw [P.attachmentChart_target, Q.attachmentChart_target]
  exact (P.collars_disjoint Q hij).mono
    (Set.image_mono positive_collar_subset) (Set.image_mono positive_collar_subset)
      |>.preimage Subtype.val

end EventCapCoordinates

end PoincareConjecture.M38
