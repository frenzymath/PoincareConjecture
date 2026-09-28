import PoincareConjecture.Proofs.M38.PartialCutCompact
import PoincareConjecture.Proofs.M07.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
  (S : Set (Fin (F.event T hT).cap_count))

noncomputable local instance partialSmoothChartedSpace :
    ChartedSpace StandardCapSpace (PartialCappedSpace F T hT P S) :=
  partialCappedChartedSpace F T hT P S

theorem partialCappingInclude_localDiffeomorph (j : PartialCappingIndex F T hT P S) :
    letI := (partialCappingDomain F T hT P S j).isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (partialCappingInclude F T hT P S j) :=
  Poincare.Gluing.include_isLocalDiffeomorph
    (fun j => (partialCappingDomain F T hT P S j : Set StandardCapSpace))
    (fun j => (partialCappingDomain F T hT P S j).isOpen) (partialCappingOverlap F T hT P S)
    (cappingOverlap_smooth _ _ _ (partialCappingMap_smooth F T hT P S)) j

theorem partialOldInclusion_localDiffeomorph :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (partialOldInclusion F T hT P S) := by
  intro y
  letI : Nonempty (partialCappingDomain F T hT P S (.inl y)) :=
    partialCappingDomain_nonempty F T hT P S (.inl y)
  letI := (partialCappingDomain F T hT P S
    (.inl y)).isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let z : partialCappingDomain F T hT P S (.inl y) :=
    ⟨chartAt StandardCapSpace y y,
      (chartAt StandardCapSpace y).map_source (mem_chart_source _ y)⟩
  let e := partialCappingMap F T hT P S (.inl y)
  let d : PartialDiffeomorph (𝓡 3) (𝓡 3)
      (partialCappingDomain F T hT P S (.inl y)) (eventCutOpen F T hT P S) ∞ := {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := (partialCappingMap_smooth F T hT P S (.inl y)).1
    contMDiffOn_invFun := (partialCappingMap_smooth F T hT P S (.inl y)).2 }
  have hd : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ e z :=
    d.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (by
      change z ∈ e.source
      rw [partialCappingMap_old_source]
      exact Set.mem_univ _)
  have heq : partialOldInclusion F T hT P S ∘ e =
      partialCappingInclude F T hT P S (.inl y) :=
    funext (partialOldInclusion_patch F T hT P S y)
  have hf : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (partialOldInclusion F T hT P S ∘ e) z := by
    rw [heq]
    exact partialCappingInclude_localDiffeomorph F T hT P S (.inl y) z
  have h := hd.of_comp hf
  change IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (partialOldInclusion F T hT P S)
    (partialCappingMap F T hT P S (.inl y) z) at h
  rwa [partialCappingMap_old_center] at h

theorem partialOldInclusion_smooth :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (partialOldInclusion F T hT P S) :=
  (partialOldInclusion_localDiffeomorph F T hT P S).contMDiff

noncomputable def partialOldInverse (q : PartialCappedSpace F T hT P S) :
    eventCutOpen F T hT P S := by
  classical
  exact if h : ∃ y, partialOldInclusion F T hT P S y = q then Classical.choose h
    else partialCappingMap F T hT P S q.out.1 q.out.2

theorem partialOldInverse_apply (y : eventCutOpen F T hT P S) :
    partialOldInverse F T hT P S (partialOldInclusion F T hT P S y) = y := by
  classical
  have h : ∃ z, partialOldInclusion F T hT P S z = partialOldInclusion F T hT P S y := ⟨y, rfl⟩
  unfold partialOldInverse
  rw [dif_pos h]
  exact (partialOldInclusion_openEmbedding F T hT P S).injective (Classical.choose_spec h)

theorem partialOldInverse_right {q : PartialCappedSpace F T hT P S}
    (hq : q ∈ Set.range (partialOldInclusion F T hT P S)) :
    partialOldInclusion F T hT P S (partialOldInverse F T hT P S q) = q := by
  obtain ⟨y, rfl⟩ := hq
  rw [partialOldInverse_apply]

theorem partialOldInverse_smooth :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (partialOldInverse F T hT P S)
      (Set.range (partialOldInclusion F T hT P S)) := by
  rintro q ⟨y, rfl⟩
  let h := partialOldInclusion_localDiffeomorph F T hT P S y
  apply ContMDiffAt.contMDiffWithinAt
  apply h.localInverse_contMDiffAt.congr_of_eventuallyEq
  filter_upwards [h.localInverse_open_source.mem_nhds h.localInverse_mem_source] with z hz
  have heq := partialOldInverse_apply F T hT P S (h.localInverse z)
  rw [h.localInverse_right_inv hz] at heq
  exact heq

end PoincareConjecture.M38
