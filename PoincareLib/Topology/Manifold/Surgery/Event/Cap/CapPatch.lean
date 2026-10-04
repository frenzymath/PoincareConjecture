import PoincareLib.Topology.Manifold.Surgery.Event.Cap.CapAnnulus
import PoincareLib.Topology.Manifold.Surgery.Event.Partial.PartialChartRestriction

/-!
# Actual cap patches over the discarded interior

The positive collar annulus is restricted to the double ball and to the
open discarded region. Its explicit graph is closed in that product,
including at the inner and outer annular ends.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M38

/-- The open double ball used as a new cap chart. -/
def capDoubleBall : TopologicalSpace.Opens StandardCapSpace :=
  ⟨Metric.ball 0 2, Metric.isOpen_ball⟩

/-- The center witnesses nonemptiness of each new chart domain. -/
theorem capDoubleBall_nonempty : Nonempty capDoubleBall :=
  ⟨⟨0, by simp [capDoubleBall]⟩⟩

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier]

/-- The old part of the capped discarded carrier has its inherited
open-submanifold structure. -/
def eventDiscardedOpen :
    TopologicalSpace.Opens (F.slice (F.event T hT).tMinus).carrier :=
  ⟨(F.event T hT).retained_preᶜ, (F.event T hT).retained_pre_compact.isClosed.isOpen_compl⟩

namespace EventCapCoordinates

variable {F T hT} {i : Fin (F.event T hT).cap_count}
  (P : EventCapCoordinates F T hT i)

include P in
/-- An actual cap has a nonempty positive collar on the discarded side. -/
theorem discarded_nonempty : Nonempty (eventDiscardedOpen F T hT) := by
  refine ⟨⟨P.collar (capUnitDirection 0, 1 / 2), ?_⟩⟩
  exact P.annular_target_discarded
    ⟨(capUnitDirection 0, 1 / 2), ⟨Set.mem_univ _, by norm_num⟩, rfl⟩

/-- The actual attachment, viewed as a partial chart from the new double
ball to the old discarded interior. -/
noncomputable def attachmentChart :
    OpenPartialHomeomorph capDoubleBall (eventDiscardedOpen F T hT) :=
  ((P.annularChart.subtypeRestr capDoubleBall_nonempty).symm.subtypeRestr
    P.discarded_nonempty).symm

/-- In the double ball, the attaching source is exactly radius above one. -/
theorem attachmentChart_source :
    P.attachmentChart.source = {x : capDoubleBall | 1 < ‖x.val‖} := by
  rw [attachmentChart, partialSubtype_both_source _ _ _ _ _
    P.annular_target_discarded]
  ext x
  change (1 < ‖x.val‖ ∧ ‖x.val‖ < 2) ↔ 1 < ‖x.val‖
  exact and_iff_left (by simpa only [capDoubleBall, TopologicalSpace.Opens.mem_mk,
    Metric.mem_ball, dist_zero_right] using x.property)

/-- Restricting the types preserves the literal positive collar target. -/
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

/-- On the actual attaching annulus the subtype map has the original
collar formula. -/
theorem attachmentChart_apply {x : capDoubleBall} (hx : 1 < ‖x.val‖) :
    (P.attachmentChart x).val = P.collar (capAttachCoordinates x.val) := by
  have hsrc : x ∈ P.attachmentChart.source := by rwa [P.attachmentChart_source]
  exact (P.annularChart.subtypeRestr capDoubleBall_nonempty).symm.subtypeRestr_symm_apply
    P.discarded_nonempty hsrc

/-- The chart's identification graph is the already proved literal
annular attachment graph, with no extra end points added. -/
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

/-- Different actual cap charts attach to disjoint parts of the old side. -/
theorem attachmentChart_targets_disjoint {j : Fin (F.event T hT).cap_count}
    (Q : EventCapCoordinates F T hT j) (hij : i ≠ j) :
    Disjoint P.attachmentChart.target Q.attachmentChart.target := by
  rw [P.attachmentChart_target, Q.attachmentChart_target]
  exact (P.collars_disjoint Q hij).mono
    (Set.image_mono positive_collar_subset) (Set.image_mono positive_collar_subset)
      |>.preimage Subtype.val

end EventCapCoordinates

end PoincareMT.M38
