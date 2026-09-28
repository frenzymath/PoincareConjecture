import PoincareConjecture.Proofs.M38.CappingCarrier
import PoincareConjecture.Proofs.M07.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)

noncomputable local instance cappedSmoothChartedSpace :
    ChartedSpace StandardCapSpace (CappedDiscardedSpace F T hT P) :=
  cappedDiscardedChartedSpace F T hT P

theorem eventCappingInclude_localDiffeomorph (j : EventCappingIndex F T hT) :
    letI := (eventCappingDomain F T hT j).isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (eventCappingInclude F T hT P j) :=
  Poincare.Gluing.include_isLocalDiffeomorph
    (fun j => (eventCappingDomain F T hT j : Set StandardCapSpace))
    (fun j => (eventCappingDomain F T hT j).isOpen) (eventCappingOverlap F T hT P)
    (cappingOverlap_smooth _ _ _ (eventCappingMap_smooth F T hT P)) j

theorem cappedOldInclusion_localDiffeomorph :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (cappedOldInclusion F T hT P) := by
  intro y
  letI : Nonempty (eventCappingDomain F T hT (.inl y)) :=
    eventCappingDomain_nonempty F T hT (.inl y)
  letI := (eventCappingDomain F T hT (.inl y)).isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let z : eventCappingDomain F T hT (.inl y) :=
    ⟨chartAt StandardCapSpace y y,
      (chartAt StandardCapSpace y).map_source (mem_chart_source _ y)⟩
  let e := eventCappingMap F T hT P (.inl y)
  let d : PartialDiffeomorph (𝓡 3) (𝓡 3)
      (eventCappingDomain F T hT (.inl y)) (eventDiscardedOpen F T hT) ∞ := {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := (eventCappingMap_smooth F T hT P (.inl y)).1
    contMDiffOn_invFun := (eventCappingMap_smooth F T hT P (.inl y)).2 }
  have hd : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ e z :=
    d.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
      (by change z ∈ e.source; rw [eventCappingMap_old_source]; exact Set.mem_univ _)
  have heq : cappedOldInclusion F T hT P ∘ e = eventCappingInclude F T hT P (.inl y) :=
    funext (cappedOldInclusion_patch F T hT P y)
  have hf : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (cappedOldInclusion F T hT P ∘ e) z := by
    rw [heq]
    exact eventCappingInclude_localDiffeomorph F T hT P (.inl y) z
  have h := hd.of_comp hf
  change IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (cappedOldInclusion F T hT P)
    (eventCappingMap F T hT P (.inl y) z) at h
  rwa [eventCappingMap_old_center] at h

theorem cappedOldInclusion_smooth :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (cappedOldInclusion F T hT P) :=
  (cappedOldInclusion_localDiffeomorph F T hT P).contMDiff

noncomputable def cappedOldInverse (q : CappedDiscardedSpace F T hT P) :
    eventDiscardedOpen F T hT := by
  classical
  exact if h : ∃ y, cappedOldInclusion F T hT P y = q then Classical.choose h
    else eventCappingMap F T hT P q.out.1 q.out.2

theorem cappedOldInverse_apply (y : eventDiscardedOpen F T hT) :
    cappedOldInverse F T hT P (cappedOldInclusion F T hT P y) = y := by
  classical
  have h : ∃ z, cappedOldInclusion F T hT P z = cappedOldInclusion F T hT P y := ⟨y, rfl⟩
  unfold cappedOldInverse
  rw [dif_pos h]
  exact (cappedOldInclusion_openEmbedding F T hT P).injective (Classical.choose_spec h)

theorem cappedOldInverse_right {q : CappedDiscardedSpace F T hT P}
    (hq : q ∈ Set.range (cappedOldInclusion F T hT P)) :
    cappedOldInclusion F T hT P (cappedOldInverse F T hT P q) = q := by
  obtain ⟨y, rfl⟩ := hq
  rw [cappedOldInverse_apply]

theorem cappedOldInverse_smooth :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (cappedOldInverse F T hT P)
      (Set.range (cappedOldInclusion F T hT P)) := by
  rintro q ⟨y, rfl⟩
  let h := cappedOldInclusion_localDiffeomorph F T hT P y
  apply ContMDiffAt.contMDiffWithinAt
  apply h.localInverse_contMDiffAt.congr_of_eventuallyEq
  filter_upwards [h.localInverse_open_source.mem_nhds h.localInverse_mem_source] with z hz
  have heq := cappedOldInverse_apply F T hT P (h.localInverse z)
  rw [h.localInverse_right_inv hz] at heq
  exact heq

end PoincareConjecture.M38
