import PoincareConjecture.Proofs.M38.SharedCutRegions
import PoincareConjecture.Proofs.M38.SharedCutLocalModels









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
  (S R : Set (Fin (F.event T hT).cap_count)) (hSR : S ⊆ R)

noncomputable local instance sharedSmoothChartedSpace
    (U : Set (Fin (F.event T hT).cap_count)) :
    ChartedSpace StandardCapSpace (PartialCappedSpace F T hT P U) :=
  partialCappedChartedSpace F T hT P U


theorem sharedCutPatch_localDiffeomorph (j : SharedCutIndex F T hT P S R) :
    letI : Nonempty (sharedCutDomain F T hT P S R hSR j) :=
      partialCappingDomain_nonempty F T hT P R (sharedCutIndex F T hT P S R hSR j)
    letI := (sharedCutDomain F T hT P S R hSR j).isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (sharedCutPatch F T hT P S R hSR j) := by
  cases j with
  | inl y =>
      letI : Nonempty (partialCappingDomain F T hT P R (.inl y)) :=
        partialCappingDomain_nonempty F T hT P R (.inl y)
      letI := (partialCappingDomain F T hT P R
        (.inl y)).isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
      intro x
      let e := partialCappingMap F T hT P R (.inl y)
      let d : PartialDiffeomorph (𝓡 3) (𝓡 3)
          (partialCappingDomain F T hT P R (.inl y)) (eventCutOpen F T hT P R) ∞ := {
        toPartialEquiv := e.toPartialEquiv
        open_source := e.open_source
        open_target := e.open_target
        contMDiffOn_toFun := (partialCappingMap_smooth F T hT P R (.inl y)).1
        contMDiffOn_invFun := (partialCappingMap_smooth F T hT P R (.inl y)).2 }
      have hd : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ e x :=
        ⟨d, by change x ∈ e.source; rw [partialCappingMap_old_source]; exact Set.mem_univ _,
          fun _ _ => rfl⟩
      have hi := openInclusion_localDiffeomorph (F.slice (F.event T hT).tMinus)
        (eventCutOpen F T hT P R) (eventCutOpen F T hT P S)
        (eventCutOpen_antitone F T hT P S R hSR) (e x)
      have ho := partialOldInclusion_localDiffeomorph F T hT P S
        (successiveOldInclusion F T hT P S R hSR (e x))
      exact hd.comp (𝓡 3) (PartialCappedSpace F T hT P S)
        (hi.comp (𝓡 3) (PartialCappedSpace F T hT P S) ho)
  | inr a =>
      exact partialCappingInclude_localDiffeomorph F T hT P S (.inr a)


theorem sharedCutComparison_localDiffeomorph :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (sharedCutComparison F T hT P S R hSR) := by
  intro p
  obtain ⟨j, x, hx⟩ := Set.mem_iUnion.mp p.property
  letI : Nonempty (sharedCutDomain F T hT P S R hSR j) :=
    partialCappingDomain_nonempty F T hT P R (sharedCutIndex F T hT P S R hSR j)
  letI := (sharedCutDomain F T hT P S R hSR j).isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let q : sharedCutDomain F T hT P S R hSR j → sharedCutOpen F T hT P S R hSR :=
    fun z => ⟨sharedCutInclude F T hT P S R hSR j z, Set.mem_iUnion.mpr ⟨j, Set.mem_range_self z⟩⟩
  have hq := openCodomain_localDiffeomorphAt (partialCappedCarrier F T hT P R)
    (sharedCutOpen F T hT P S R hSR) q x
    (partialCappingInclude_localDiffeomorph F T hT P R (sharedCutIndex F T hT P S R hSR j) x)
  have heq : sharedCutComparison F T hT P S R hSR ∘ q =
      sharedCutPatch F T hT P S R hSR j :=
    funext (sharedCutComparison_patch F T hT P S R hSR j)
  have h := hq.of_comp (f := sharedCutComparison F T hT P S R hSR) (by
    rw [heq]
    exact sharedCutPatch_localDiffeomorph F T hT P S R hSR j x)
  have hp : q x = p := Subtype.ext hx
  rwa [hp] at h

end PoincareConjecture.M38
