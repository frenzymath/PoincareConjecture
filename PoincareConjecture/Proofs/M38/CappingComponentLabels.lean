import PoincareConjecture.Proofs.M38.CappingCompact
import Mathlib.Topology.Connected.TotallyDisconnected









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38


noncomputable def capAnnularPoint : capDoubleBall :=
  ⟨(3 / 2 : ℝ) • (capUnitDirection (0 : StandardCapSpace)).val, by
    change dist ((3 / 2 : ℝ) • (capUnitDirection (0 : StandardCapSpace)).val) 0 < 2
    rw [dist_zero_right, norm_smul]
    norm_num⟩


theorem capAnnularPoint_norm : ‖capAnnularPoint.val‖ = (3 / 2 : ℝ) := by
  dsimp only [capAnnularPoint]
  rw [norm_smul]
  norm_num


theorem capDoubleBall_connected : ConnectedSpace capDoubleBall :=
  isConnected_iff_connectedSpace.mp (Metric.isConnected_ball (by norm_num : (0 : ℝ) < 2))

variable {F : SurgeryFlowData.{u}} {T : ℝ} {hT : T ∈ F.surgery_times}
  [Nonempty (F.slice T).carrier]

namespace EventCapCoordinates

variable {i : Fin (F.event T hT).cap_count} (P : EventCapCoordinates F T hT i)


theorem capAnnularPoint_mem : capAnnularPoint ∈ P.attachmentChart.source := by
  rw [P.attachmentChart_source]
  change 1 < ‖capAnnularPoint.val‖
  rw [capAnnularPoint_norm]
  norm_num


noncomputable def attachmentPoint : eventDiscardedOpen F T hT :=
  P.attachmentChart capAnnularPoint


theorem attachmentPoint_mem : P.attachmentPoint ∈ P.attachmentChart.target :=
  P.attachmentChart.map_source P.capAnnularPoint_mem



theorem attachmentChart_target_connected : IsConnected P.attachmentChart.target := by
  let : ConnectedSpace UnitTwoSphere :=
    isConnected_iff_connectedSpace.mp
      (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp)) _ zero_le_one)
  let : ConnectedSpace (Set.Ioo (0 : ℝ) 1) :=
    isConnected_iff_connectedSpace.mp (isConnected_Ioo zero_lt_one)
  let f : UnitTwoSphere × Set.Ioo (0 : ℝ) 1 → eventDiscardedOpen F T hT :=
    fun z => ⟨P.collar (z.1, z.2.val), P.annular_target_discarded
      ⟨(z.1, z.2.val), ⟨Set.mem_univ _, z.2.property⟩, rfl⟩⟩
  have hf : Continuous f := by
    have hg : Continuous (fun z : UnitTwoSphere × Set.Ioo (0 : ℝ) 1 =>
        (z.1, z.2.val)) := continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
    have hc := (event_cap_collar_smooth F T hT i P.width_pos P.width_lt
      P.shell_domain).continuousOn
    exact (hc.comp_continuous hg (fun z => positive_collar_subset
      ⟨Set.mem_univ _, z.2.property⟩)).subtype_mk _
  have hrange : Set.range f = P.attachmentChart.target := by
    rw [P.attachmentChart_target]
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨(z.1, z.2.val), ⟨Set.mem_univ _, z.2.property⟩, rfl⟩
    · rintro ⟨⟨z, s⟩, ⟨_, hs⟩, hxs⟩
      exact ⟨(z, ⟨s, hs⟩), Subtype.ext hxs⟩
  rw [← hrange]
  exact isConnected_range hf



theorem attachment_component_eq {x : eventDiscardedOpen F T hT}
    (hx : x ∈ P.attachmentChart.target) :
    ConnectedComponents.mk x = ConnectedComponents.mk P.attachmentPoint :=
  ConnectedComponents.coe_eq_coe'.mpr
    (P.attachmentChart_target_connected.subset_connectedComponent P.attachmentPoint_mem hx)

end EventCapCoordinates

variable (F T hT) (P : ∀ i, EventCapCoordinates F T hT i)



noncomputable def eventCappingComponentLabel :
    (j : EventCappingIndex F T hT) → eventCappingDomain F T hT j →
      ConnectedComponents (eventDiscardedOpen F T hT)
  | .inl x, z => ConnectedComponents.mk (eventCappingMap F T hT P (.inl x) z)
  | .inr i, _ => ConnectedComponents.mk (P i).attachmentPoint


theorem eventCappingComponentLabel_source (j : EventCappingIndex F T hT)
    {x : eventCappingDomain F T hT j}
    (hx : x ∈ (eventCappingMap F T hT P j).source) :
    eventCappingComponentLabel F T hT P j x =
      ConnectedComponents.mk (eventCappingMap F T hT P j x) := by
  cases j with
  | inl y => rfl
  | inr i =>
      exact ((P i).attachment_component_eq ((P i).attachmentChart.map_source hx)).symm


theorem eventCappingComponentLabel_rel
    (a b : Sigma (fun j => eventCappingDomain F T hT j))
    (hab : (eventCappingOverlap F T hT P).Rel a b) :
    eventCappingComponentLabel F T hT P a.1 a.2 =
      eventCappingComponentLabel F T hT P b.1 b.2 := by
  rcases a with ⟨j, x⟩
  rcases b with ⟨k, y⟩
  by_cases hjk : j = k
  · subst k
    have hxy : x = y := by
      simpa only [Poincare.Gluing.OverlapSystem.Rel, eventCappingOverlap,
        cappingOverlap, cappingTransition_self, OpenPartialHomeomorph.refl_apply,
        id_eq] using hab.2
    exact congrArg (eventCappingComponentLabel F T hT P j) hxy
  · have h := (cappingTransition_graph (eventCappingMap F T hT P) hjk x y).mp hab
    rw [eventCappingComponentLabel_source F T hT P j h.1,
      eventCappingComponentLabel_source F T hT P k h.2.1, h.2.2]


noncomputable def cappedComponentLabel :
    CappedDiscardedSpace F T hT P → ConnectedComponents (eventDiscardedOpen F T hT) :=
  Quotient.lift (fun a => eventCappingComponentLabel F T hT P a.1 a.2)
    (eventCappingComponentLabel_rel F T hT P)


theorem cappedComponentLabel_patch (j : EventCappingIndex F T hT)
    (x : eventCappingDomain F T hT j) :
    cappedComponentLabel F T hT P (eventCappingInclude F T hT P j x) =
      eventCappingComponentLabel F T hT P j x := rfl



theorem eventCappingComponentLabel_continuous (j : EventCappingIndex F T hT) :
    Continuous (eventCappingComponentLabel F T hT P j) := by
  cases j with
  | inl x =>
      exact ConnectedComponents.continuous_coe.comp
        (eventCappingMap_old_openEmbedding F T hT P x).continuous
  | inr i => exact continuous_const


theorem cappedComponentLabel_continuous : Continuous (cappedComponentLabel F T hT P) :=
  (continuous_sigma (eventCappingComponentLabel_continuous F T hT P)).quotient_lift
    (eventCappingComponentLabel_rel F T hT P)


theorem cappedComponentLabel_old (x : eventDiscardedOpen F T hT) :
    cappedComponentLabel F T hT P (cappedOldInclusion F T hT P x) =
      ConnectedComponents.mk x := by
  let z : eventCappingDomain F T hT (.inl x) :=
    ⟨chartAt StandardCapSpace x x,
      (chartAt StandardCapSpace x).map_source (mem_chart_source _ x)⟩
  have h := cappedOldInclusion_patch F T hT P x z
  rw [eventCappingMap_old_center] at h
  rw [h, cappedComponentLabel_patch]
  change ConnectedComponents.mk (eventCappingMap F T hT P (.inl x) z) = _
  rw [eventCappingMap_old_center]

end PoincareConjecture.M38
