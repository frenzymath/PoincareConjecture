import PoincareConjecture.Proofs.M38.FullCutPost
import PoincareConjecture.Proofs.M38.FullCutDiscarded
import PoincareConjecture.Proofs.M38.FullCutLocalModels

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)

noncomputable local instance fullSmoothPartialChartedSpace :
    ChartedSpace StandardCapSpace (PartialCappedSpace F T hT P Set.univ) :=
  partialCappedChartedSpace F T hT P Set.univ

noncomputable local instance fullSmoothDiscardedChartedSpace :
    ChartedSpace StandardCapSpace (CappedDiscardedSpace F T hT P) :=
  cappedDiscardedChartedSpace F T hT P

noncomputable def retentionInteriorDiffeomorph :
    Diffeomorph (𝓡 3) (𝓡 3)
      (eventRetainedInteriorOpen F T hT) (eventCapComplementOpen F T hT) ∞ where
  toEquiv := (retentionInteriorHomeomorph F T hT).toEquiv
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (eventCapComplementOpen F T hT)
      (retentionInteriorHomeomorph F T hT)).mp
    exact (retentionInteriorEquivalence F T hT).map_smooth.comp_contMDiff
      contMDiff_subtype_val (fun x => x.property)
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff (eventRetainedInteriorOpen F T hT)
      (retentionInteriorHomeomorph F T hT).symm).mp
    exact (retentionInteriorEquivalence F T hT).inverse_smooth.comp_contMDiff
      contMDiff_subtype_val (fun x => x.property)

theorem fullCutPostOld_localDiffeomorph :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fullCutPostOld F T hT P) := by
  intro x
  exact ((retentionInteriorDiffeomorph F T hT).symm.isLocalDiffeomorph x).comp
    (𝓡 3) (eventCutOpen F T hT P Set.univ)
    (openInclusion_localDiffeomorph (F.slice (F.event T hT).tMinus)
      (eventRetainedInteriorOpen F T hT) (eventCutOpen F T hT P Set.univ)
      (retained_subset_fullCut F T hT P) ((retentionInteriorHomeomorph F T hT).symm x))

theorem fullCutPostInclusion_localDiffeomorph :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fullCutPostInclusion F T hT P) := by
  intro p
  obtain ⟨j, hj⟩ := retainedPatch_cover F T hT P p
  have hp := mem_of_mem_nhds hj
  cases j with
  | none =>
      let x : eventCapComplementOpen F T hT := ⟨p, hp⟩
      have hq := openSubtype_localDiffeomorph (F.slice T) (eventCapComplementOpen F T hT) x
      have hf := (fullCutPostOld_localDiffeomorph F T hT P x).comp
        (𝓡 3) (PartialCappedSpace F T hT P Set.univ)
        (partialOldInclusion_localDiffeomorph F T hT P Set.univ (fullCutPostOld F T hT P x))
      have heq : fullCutPostInclusion F T hT P ∘
          (Subtype.val : eventCapComplementOpen F T hT → (F.slice T).carrier) =
            partialOldInclusion F T hT P Set.univ ∘ fullCutPostOld F T hT P :=
        funext (fullCutPostInclusion_old F T hT P)
      exact hq.of_comp (f := fullCutPostInclusion F T hT P) (by rw [heq]; exact hf)
  | some i =>
      obtain ⟨z, hz, hzp⟩ := hp
      let x : capDoubleBall := ⟨z, hz⟩
      letI : Nonempty capDoubleBall := capDoubleBall_nonempty
      letI := capDoubleBall.isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
      have hq := surgeryBall_patch_localDiffeomorph (F.slice T) (P i).ball x
      have heq : fullCutPostInclusion F T hT P ∘ (fun x : capDoubleBall => (P i).ball.map x.val) =
          partialCappingInclude F T hT P Set.univ (.inr (⟨i, Set.mem_univ i⟩, false)) :=
        funext (fullCutPostInclusion_cap F T hT P i)
      have h := hq.of_comp (f := fullCutPostInclusion F T hT P) (by
        rw [heq]
        exact partialCappingInclude_localDiffeomorph F T hT P Set.univ
          (.inr (⟨i, Set.mem_univ i⟩, false)) x)
      change IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (fullCutPostInclusion F T hT P)
        ((P i).ball.map z) at h
      rwa [hzp] at h

theorem fullCutDiscardedPatch_localDiffeomorph (j : EventCappingIndex F T hT) :
    letI := (eventCappingDomain F T hT j).isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fullCutDiscardedPatch F T hT P j) := by
  cases j with
  | inl y =>
      letI : Nonempty (eventCappingDomain F T hT (.inl y)) :=
        eventCappingDomain_nonempty F T hT (.inl y)
      letI := (eventCappingDomain F T hT
        (.inl y)).isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
      intro x
      let e := eventCappingMap F T hT P (.inl y)
      let d : PartialDiffeomorph (𝓡 3) (𝓡 3)
          (eventCappingDomain F T hT (.inl y)) (eventDiscardedOpen F T hT) ∞ := {
        toPartialEquiv := e.toPartialEquiv
        open_source := e.open_source
        open_target := e.open_target
        contMDiffOn_toFun := (eventCappingMap_smooth F T hT P (.inl y)).1
        contMDiffOn_invFun := (eventCappingMap_smooth F T hT P (.inl y)).2 }
      have hd : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ e x :=
        ⟨d, by change x ∈ e.source; rw [eventCappingMap_old_source]; exact Set.mem_univ _,
          fun _ _ => rfl⟩
      have hi := openInclusion_localDiffeomorph (F.slice (F.event T hT).tMinus)
        (eventDiscardedOpen F T hT) (eventCutOpen F T hT P Set.univ)
        (discarded_subset_fullCut F T hT P) (e x)
      have ho := partialOldInclusion_localDiffeomorph F T hT P Set.univ
        (fullCutDiscarded F T hT P (e x))
      exact hd.comp (𝓡 3) (PartialCappedSpace F T hT P Set.univ)
        (hi.comp (𝓡 3) (PartialCappedSpace F T hT P Set.univ) ho)
  | inr i =>
      exact partialCappingInclude_localDiffeomorph F T hT P Set.univ
        (.inr (⟨i, Set.mem_univ i⟩, true))

theorem fullCutDiscardedInclusion_localDiffeomorph :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fullCutDiscardedInclusion F T hT P) := by
  intro p
  induction p using Quotient.inductionOn with
  | h a =>
      rcases a with ⟨j, x⟩
      letI := (eventCappingDomain F T hT j).isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
      have hq := eventCappingInclude_localDiffeomorph F T hT P j x
      have heq : fullCutDiscardedInclusion F T hT P ∘ eventCappingInclude F T hT P j =
          fullCutDiscardedPatch F T hT P j :=
        funext (fullCutDiscardedInclusion_patch F T hT P j)
      exact hq.of_comp (f := fullCutDiscardedInclusion F T hT P) (by
        rw [heq]
        exact fullCutDiscardedPatch_localDiffeomorph F T hT P j x)

end PoincareConjecture.M38
