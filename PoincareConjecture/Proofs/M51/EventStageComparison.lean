import PoincareConjecture.Proofs.M51.GlobalRepresentatives
import PoincareConjecture.Proofs.M51.EventIntervals











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M51.CompletedStageChain

variable {S : RepairedControlledSchedulesData.{u}}
  {N : RepairedNoncollapseInductionData S}
  {C : RepairedCanonicalInductionData S N}
  {F0 : SurgeryFlowData.{u}} {k : ℕ}
  (Q : CompletedStageChain S N C F0 k)


theorem stageEvent_reference (n m : ℕ) (T : ℝ)
    (hTn : T ∈ (Q.flow n).surgery_times) (hTm : T ∈ (Q.flow m).surgery_times)
    [Nonempty ((Q.flow n).slice T).carrier] [Nonempty ((Q.flow m).slice T).carrier] :
    ((Q.flow m).event T hTm).tMinus = ((Q.flow n).event T hTn).tMinus := by
  let q := max n m
  have hnq : n ≤ q := le_max_left _ _
  have hmq : m ≤ q := le_max_right _ _
  have hTq := (ComposedExtension.oldSurgeryTimeTo (Q.extensionBetween n q hnq)
    (Q.extensionBetween_eq n q hnq) T ((Q.flow n).surgery_times_subset hTn)).mpr hTn
  let : Nonempty ((Q.flow q).slice T).carrier := by
    obtain ⟨x⟩ := ‹Nonempty ((Q.flow n).slice T).carrier›
    exact ⟨Q.stageIdentify n q hnq T ((Q.flow n).surgery_times_subset hTn) x⟩
  exact (ComposedExtension.oldEventReferenceTo (Q.extensionBetween m q hmq)
    (Q.extensionBetween_eq m q hmq) T hTm hTq).symm.trans
      (ComposedExtension.oldEventReferenceTo (Q.extensionBetween n q hnq)
        (Q.extensionBetween_eq n q hnq) T hTn hTq)


theorem stageVanishing_reference (n m : ℕ) (T : ℝ)
    (hTn : T ∈ (Q.flow n).surgery_times) (hTm : T ∈ (Q.flow m).surgery_times)
    [IsEmpty ((Q.flow n).slice T).carrier] [IsEmpty ((Q.flow m).slice T).carrier] :
    ((Q.flow m).vanishing_event T hTm).tMinus =
      ((Q.flow n).vanishing_event T hTn).tMinus := by
  let q := max n m
  have hnq : n ≤ q := le_max_left _ _
  have hmq : m ≤ q := le_max_right _ _
  have hTq := (ComposedExtension.oldSurgeryTimeTo (Q.extensionBetween n q hnq)
    (Q.extensionBetween_eq n q hnq) T ((Q.flow n).surgery_times_subset hTn)).mpr hTn
  let : IsEmpty ((Q.flow q).slice T).carrier :=
    ⟨fun x => isEmptyElim
      ((Q.stageIdentify n q hnq T ((Q.flow n).surgery_times_subset hTn)).symm x)⟩
  exact (ComposedExtension.oldVanishingReferenceTo (Q.extensionBetween m q hmq)
    (Q.extensionBetween_eq m q hmq) T hTm hTq).symm.trans
      (ComposedExtension.oldVanishingReferenceTo (Q.extensionBetween n q hnq)
        (Q.extensionBetween_eq n q hnq) T hTn hTq)


theorem stageEvent_retained_post (n m : ℕ) (T : ℝ)
    (hTn : T ∈ (Q.flow n).surgery_times) (hTm : T ∈ (Q.flow m).surgery_times)
    [Nonempty ((Q.flow n).slice T).carrier] [Nonempty ((Q.flow m).slice T).carrier] :
    Q.compare n m T ((Q.flow n).surgery_times_subset hTn)
        ((Q.flow m).surgery_times_subset hTm) '' ((Q.flow n).event T hTn).retained_post =
      ((Q.flow m).event T hTm).retained_post := by
  let q := max n m
  have hnq : n ≤ q := le_max_left _ _
  have hmq : m ≤ q := le_max_right _ _
  have hTq := (ComposedExtension.oldSurgeryTimeTo (Q.extensionBetween n q hnq)
    (Q.extensionBetween_eq n q hnq) T ((Q.flow n).surgery_times_subset hTn)).mpr hTn
  let : Nonempty ((Q.flow q).slice T).carrier := by
    obtain ⟨x⟩ := ‹Nonempty ((Q.flow n).slice T).carrier›
    exact ⟨Q.stageIdentify n q hnq T ((Q.flow n).surgery_times_subset hTn) x⟩
  have hn := ComposedExtension.oldRetainedPostTo (Q.extensionBetween n q hnq)
    (Q.extensionBetween_eq n q hnq) T hTn hTq
  have hm := ComposedExtension.oldRetainedPostTo (Q.extensionBetween m q hmq)
    (Q.extensionBetween_eq m q hmq) T hTm hTq
  apply Set.image_injective.mpr
    (Q.stageIdentify m q hmq T ((Q.flow m).surgery_times_subset hTm)).injective
  calc
    _ = Q.stageIdentify n q hnq T ((Q.flow n).surgery_times_subset hTn) ''
        ((Q.flow n).event T hTn).retained_post := by
      rw [Set.image_image]
      congr 1
      funext x
      exact Q.compare_common n m q hnq hmq T
        ((Q.flow n).surgery_times_subset hTn) ((Q.flow m).surgery_times_subset hTm) x
    _ = ((Q.flow q).event T hTq).retained_post := hn
    _ = _ := hm.symm


noncomputable def stageEventPreCompare (n m : ℕ) (T : ℝ)
    (hTn : T ∈ (Q.flow n).surgery_times) (hTm : T ∈ (Q.flow m).surgery_times)
    [Nonempty ((Q.flow n).slice T).carrier] [Nonempty ((Q.flow m).slice T).carrier]
    (t : Ico ((Q.flow n).event T hTn).tMinus T) (ht : t.1 ∈ (Q.flow n).time_domain)
    (ht' : t.1 ∈ Ico ((Q.flow m).event T hTm).tMinus T) :
    Diffeomorph (𝓡 3) (𝓡 3)
      ((Q.flow n).slice ((Q.flow n).event T hTn).tMinus).carrier
      ((Q.flow m).slice ((Q.flow m).event T hTm).tMinus).carrier ∞ :=
  (((Q.flow n).event T hTn).pre_identify t).trans
    ((Q.compare n m t.1 ht ((Q.flow m).nonemptyEventPreInterval T hTm ht')).trans
      (((Q.flow m).event T hTm).pre_identify ⟨t.1, ht'⟩).symm)



theorem stageEvent_retained_pre (n m : ℕ) (T : ℝ)
    (hTn : T ∈ (Q.flow n).surgery_times) (hTm : T ∈ (Q.flow m).surgery_times)
    [Nonempty ((Q.flow n).slice T).carrier] [Nonempty ((Q.flow m).slice T).carrier]
    (t : Ico ((Q.flow n).event T hTn).tMinus T) (ht : t.1 ∈ (Q.flow n).time_domain)
    (ht' : t.1 ∈ Ico ((Q.flow m).event T hTm).tMinus T) :
    Q.stageEventPreCompare n m T hTn hTm t ht ht' ''
        ((Q.flow n).event T hTn).retained_pre =
      ((Q.flow m).event T hTm).retained_pre := by
  let q := max n m
  have hnq : n ≤ q := le_max_left _ _
  have hmq : m ≤ q := le_max_right _ _
  have hTq := (ComposedExtension.oldSurgeryTimeTo (Q.extensionBetween n q hnq)
    (Q.extensionBetween_eq n q hnq) T ((Q.flow n).surgery_times_subset hTn)).mpr hTn
  let : Nonempty ((Q.flow q).slice T).carrier := by
    obtain ⟨x⟩ := ‹Nonempty ((Q.flow n).slice T).carrier›
    exact ⟨Q.stageIdentify n q hnq T ((Q.flow n).surgery_times_subset hTn) x⟩
  have href := ComposedExtension.oldEventReferenceTo (Q.extensionBetween n q hnq)
    (Q.extensionBetween_eq n q hnq) T hTn hTq
  have htq : t.1 ∈ Ico ((Q.flow q).event T hTq).tMinus T := by
    rw [href]
    exact t.2
  have htm := (Q.flow m).nonemptyEventPreInterval T hTm ht'
  let f := (((Q.flow m).event T hTm).pre_identify ⟨t.1, ht'⟩).trans
    ((Q.stageIdentify m q hmq t.1 htm).trans
      (((Q.flow q).event T hTq).pre_identify ⟨t.1, htq⟩).symm)
  let g := (((Q.flow n).event T hTn).pre_identify t).trans
    ((Q.stageIdentify n q hnq t.1 ht).trans
      (((Q.flow q).event T hTq).pre_identify ⟨t.1, htq⟩).symm)
  have hf : f '' ((Q.flow m).event T hTm).retained_pre =
      ((Q.flow q).event T hTq).retained_pre :=
    ComposedExtension.oldRetainedPreTo (Q.extensionBetween m q hmq)
      (Q.extensionBetween_eq m q hmq) T hTm hTq ⟨t.1, ht'⟩ htm htq
  have hg : g '' ((Q.flow n).event T hTn).retained_pre =
      ((Q.flow q).event T hTq).retained_pre :=
    ComposedExtension.oldRetainedPreTo (Q.extensionBetween n q hnq)
      (Q.extensionBetween_eq n q hnq) T hTn hTq t ht htq
  have hcomp : ∀ x, f (Q.stageEventPreCompare n m T hTn hTm t ht ht' x) = g x := by
    intro x
    simp only [f, g, stageEventPreCompare, Diffeomorph.coe_trans, Function.comp_apply,
      Diffeomorph.apply_symm_apply]
    exact congrArg (((Q.flow q).event T hTq).pre_identify ⟨t.1, htq⟩).symm
      (Q.compare_common n m q hnq hmq t.1 ht htm _)
  apply Set.image_injective.mpr f.injective
  calc
    _ = g '' ((Q.flow n).event T hTn).retained_pre := by
      rw [Set.image_image]
      congr 1
      funext x
      exact hcomp x
    _ = ((Q.flow q).event T hTq).retained_pre := hg
    _ = _ := hf.symm


theorem stageEvent_retention (n m : ℕ) (T : ℝ)
    (hTn : T ∈ (Q.flow n).surgery_times) (hTm : T ∈ (Q.flow m).surgery_times)
    [Nonempty ((Q.flow n).slice T).carrier] [Nonempty ((Q.flow m).slice T).carrier]
    (t : Ico ((Q.flow n).event T hTn).tMinus T) (ht : t.1 ∈ (Q.flow n).time_domain)
    (ht' : t.1 ∈ Ico ((Q.flow m).event T hTm).tMinus T)
    (x : ((Q.flow n).slice ((Q.flow n).event T hTn).tMinus).carrier)
    (hx : x ∈ ((Q.flow n).event T hTn).retained_pre) :
    Q.compare n m T ((Q.flow n).surgery_times_subset hTn)
        ((Q.flow m).surgery_times_subset hTm) (((Q.flow n).event T hTn).retention.map x) =
      ((Q.flow m).event T hTm).retention.map
        (Q.stageEventPreCompare n m T hTn hTm t ht ht' x) := by
  let q := max n m
  have hnq : n ≤ q := le_max_left _ _
  have hmq : m ≤ q := le_max_right _ _
  have hTq := (ComposedExtension.oldSurgeryTimeTo (Q.extensionBetween n q hnq)
    (Q.extensionBetween_eq n q hnq) T ((Q.flow n).surgery_times_subset hTn)).mpr hTn
  let : Nonempty ((Q.flow q).slice T).carrier := by
    obtain ⟨x⟩ := ‹Nonempty ((Q.flow n).slice T).carrier›
    exact ⟨Q.stageIdentify n q hnq T ((Q.flow n).surgery_times_subset hTn) x⟩
  have href := ComposedExtension.oldEventReferenceTo (Q.extensionBetween n q hnq)
    (Q.extensionBetween_eq n q hnq) T hTn hTq
  have htq : t.1 ∈ Ico ((Q.flow q).event T hTq).tMinus T := by
    rw [href]
    exact t.2
  have htm := (Q.flow m).nonemptyEventPreInterval T hTm ht'
  have hxm : Q.stageEventPreCompare n m T hTn hTm t ht ht' x ∈
      ((Q.flow m).event T hTm).retained_pre := by
    rw [← Q.stageEvent_retained_pre n m T hTn hTm t ht ht']
    exact mem_image_of_mem _ hx
  have hn := ComposedExtension.oldRetentionTo (Q.extensionBetween n q hnq)
    (Q.extensionBetween_eq n q hnq) T hTn hTq t ht htq x hx
  have hm := ComposedExtension.oldRetentionTo (Q.extensionBetween m q hmq)
    (Q.extensionBetween_eq m q hmq) T hTm hTq ⟨t.1, ht'⟩ htm htq
      (Q.stageEventPreCompare n m T hTn hTm t ht ht' x) hxm
  have hmid :
      ((Q.flow q).event T hTq).retention.map
        ((((Q.flow q).event T hTq).pre_identify ⟨t.1, htq⟩).symm
          (Q.stageIdentify n q hnq t.1 ht (((Q.flow n).event T hTn).pre_identify t x))) =
      ((Q.flow q).event T hTq).retention.map
        ((((Q.flow q).event T hTq).pre_identify ⟨t.1, htq⟩).symm
          (Q.stageIdentify m q hmq t.1 htm
            (((Q.flow m).event T hTm).pre_identify ⟨t.1, ht'⟩
              (Q.stageEventPreCompare n m T hTn hTm t ht ht' x)))) := by
    apply congrArg ((Q.flow q).event T hTq).retention.map
    apply congrArg (((Q.flow q).event T hTq).pre_identify ⟨t.1, htq⟩).symm
    simp only [stageEventPreCompare, Diffeomorph.coe_trans, Function.comp_apply,
      Diffeomorph.apply_symm_apply]
    exact (Q.compare_common n m q hnq hmq t.1 ht htm _).symm
  apply (Q.stageIdentify m q hmq T ((Q.flow m).surgery_times_subset hTm)).injective
  exact (Q.compare_common n m q hnq hmq T ((Q.flow n).surgery_times_subset hTn)
    ((Q.flow m).surgery_times_subset hTm) _).trans (hn.trans (hmid.trans hm.symm))

end PoincareConjecture.M51.CompletedStageChain
