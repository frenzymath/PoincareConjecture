import PoincareConjecture.Proofs.M38.PartialCutRegions
import PoincareConjecture.Proofs.M38.CappingRegions









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)


theorem partialOldInclusion_eq_cap_iff
    (S : Set (Fin (F.event T hT).cap_count)) (y : eventCutOpen F T hT P S)
    (a : S × Bool) (x : capDoubleBall) :
    partialOldInclusion F T hT P S y = partialCappingInclude F T hT P S (.inr a) x ↔
      1 < ‖x.val‖ ∧ y = cutAttachmentChart F T hT P S a x := by
  constructor
  · intro h
    let z : partialCappingDomain F T hT P S (.inl y) :=
      ⟨chartAt StandardCapSpace y y,
        (chartAt StandardCapSpace y).map_source (mem_chart_source _ y)⟩
    have hz := partialOldInclusion_patch F T hT P S y z
    rw [partialCappingMap_old_center] at hz
    have hrel := (partialCappingOverlap F T hT P S).include_eq_iff (.inl y) (.inr a) z x
      |>.mp (hz.symm.trans h)
    have hc := (cappingTransition_graph (partialCappingMap F T hT P S)
      (i := .inl y) (j := .inr a) (by simp) z x).mp hrel
    have hx := hc.2.1
    change x ∈ (cutAttachmentChart F T hT P S a).source at hx
    rw [cutAttachmentChart_source] at hx
    refine ⟨hx, ?_⟩
    have heq := hc.2.2
    change partialCappingMap F T hT P S (.inl y) z =
      cutAttachmentChart F T hT P S a x at heq
    rwa [partialCappingMap_old_center] at heq
  · rintro ⟨hx, rfl⟩
    exact partialOldInclusion_cap F T hT P S a x hx


theorem cappedOldInclusion_eq_cap_iff (y : eventDiscardedOpen F T hT)
    (i : Fin (F.event T hT).cap_count) (x : capDoubleBall) :
    cappedOldInclusion F T hT P y = eventCappingInclude F T hT P (.inr i) x ↔
      1 < ‖x.val‖ ∧ y = (P i).attachmentChart x := by
  constructor
  · intro h
    let z : eventCappingDomain F T hT (.inl y) :=
      ⟨chartAt StandardCapSpace y y,
        (chartAt StandardCapSpace y).map_source (mem_chart_source _ y)⟩
    have hz := cappedOldInclusion_patch F T hT P y z
    rw [eventCappingMap_old_center] at hz
    have hrel := (eventCappingOverlap F T hT P).include_eq_iff (.inl y) (.inr i) z x
      |>.mp (hz.symm.trans h)
    have hc := (cappingTransition_graph (eventCappingMap F T hT P)
      (i := .inl y) (j := .inr i) (by simp) z x).mp hrel
    have hx := hc.2.1
    change x ∈ (P i).attachmentChart.source at hx
    rw [(P i).attachmentChart_source] at hx
    refine ⟨hx, ?_⟩
    have heq := hc.2.2
    change eventCappingMap F T hT P (.inl y) z = (P i).attachmentChart x at heq
    rwa [eventCappingMap_old_center] at heq
  · rintro ⟨hx, rfl⟩
    exact cappedOldInclusion_cap F T hT P i x hx

end PoincareConjecture.M38
