import PoincareConjecture.Proofs.M51.GlobalVanishingEvents
import PoincareConjecture.Proofs.M51.EventStageComparison

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

theorem globalIdentify_compare (n m : ℕ) (t : ℝ)
    (hn : t ∈ (Q.flow n).time_domain) (hm : t ∈ (Q.flow m).time_domain)
    (x : ((Q.flow n).slice t).carrier) :
    Q.globalIdentify m t hm (Q.compare n m t hn hm x) = Q.globalIdentify n t hn x := by
  let q := max n m
  have hnq : n ≤ q := le_max_left _ _
  have hmq : m ≤ q := le_max_right _ _
  calc
    _ = Q.globalIdentify q t (Q.stageTime m q hmq hm)
        (Q.stageIdentify m q hmq t hm (Q.compare n m t hn hm x)) :=
      (Q.globalIdentify_comp m q hmq t hm _).symm
    _ = Q.globalIdentify q t (Q.stageTime n q hnq hn)
        (Q.stageIdentify n q hnq t hn x) :=
      congrArg (Q.globalIdentify q t (Q.stageTime n q hnq hn))
        (Q.compare_common n m q hnq hmq t hn hm x)
    _ = _ := Q.globalIdentify_comp n q hnq t hn x

theorem globalEvent_old_reference (n : ℕ) (T : ℝ)
    (hT : T ∈ (Q.flow n).surgery_times) (hT' : T ∈ Q.globalSurgeryTimes)
    [Nonempty ((Q.flow n).slice T).carrier] [Nonempty (Q.globalSlice T).carrier] :
    (Q.globalEvent T hT').tMinus = ((Q.flow n).event T hT).tMinus := by
  let := Q.eventStageNonempty T hT'
  exact Q.stageEvent_reference n (Q.representativeIndex T) T hT (Q.eventStageSurgery T hT')

theorem globalVanishingEvent_old_reference
    (m13 : GeneralizedParabolicRescalingTheory.{u} 3) (n : ℕ) (T : ℝ)
    (hT : T ∈ (Q.flow n).surgery_times) (hT' : T ∈ Q.globalSurgeryTimes)
    [IsEmpty ((Q.flow n).slice T).carrier] [IsEmpty (Q.globalSlice T).carrier] :
    (Q.globalVanishingEvent m13 T hT').tMinus =
      ((Q.flow n).vanishing_event T hT).tMinus := by
  let := Q.eventStageIsEmpty T hT'
  exact Q.stageVanishing_reference n (Q.representativeIndex T) T hT
    (Q.eventStageSurgery T hT')

theorem globalEvent_old_retained_post (n : ℕ) (T : ℝ)
    (hT : T ∈ (Q.flow n).surgery_times) (hT' : T ∈ Q.globalSurgeryTimes)
    [Nonempty ((Q.flow n).slice T).carrier] [Nonempty (Q.globalSlice T).carrier] :
    Q.globalIdentify n T ((Q.flow n).surgery_times_subset hT) ''
      ((Q.flow n).event T hT).retained_post = (Q.globalEvent T hT').retained_post := by
  let := Q.eventStageNonempty T hT'
  rw [Q.globalEvent_retained_post]
  have hcompare := Q.stageEvent_retained_post n (Q.representativeIndex T) T hT
    (Q.eventStageSurgery T hT')
  calc
    _ = Q.globalEventPostMap T hT' ''
        (Q.compare n (Q.representativeIndex T) T ((Q.flow n).surgery_times_subset hT)
          (Q.eventStageTime T hT') '' ((Q.flow n).event T hT).retained_post) := by
      rw [Set.image_image]
      congr 1
      funext x
      exact (Q.globalIdentify_compare n (Q.representativeIndex T) T
        ((Q.flow n).surgery_times_subset hT) (Q.eventStageTime T hT') x).symm
    _ = _ := congrArg (fun A => Q.globalEventPostMap T hT' '' A) hcompare

private theorem globalEvent_pre_coordinate (n : ℕ) (T : ℝ)
    (hT : T ∈ (Q.flow n).surgery_times) (hT' : T ∈ Q.globalSurgeryTimes)
    [Nonempty ((Q.flow n).slice T).carrier] [Nonempty (Q.globalSlice T).carrier]
    [Nonempty ((Q.flow (Q.representativeIndex T)).slice T).carrier]
    (t : Ico ((Q.flow n).event T hT).tMinus T) (ht : t.1 ∈ (Q.flow n).time_domain)
    (ht' : t.1 ∈ Ico (Q.globalEvent T hT').tMinus T)
    (x : ((Q.flow n).slice ((Q.flow n).event T hT).tMinus).carrier) :
    ((Q.globalEvent T hT').pre_identify ⟨t.1, ht'⟩).symm
        (Q.globalIdentify n t.1 ht (((Q.flow n).event T hT).pre_identify t x)) =
      Q.globalEventInitialMap T hT'
        (Q.stageEventPreCompare n (Q.representativeIndex T) T hT
          (Q.eventStageSurgery T hT') t ht ht' x) := by
  let y := Q.stageEventPreCompare n (Q.representativeIndex T) T hT
    (Q.eventStageSurgery T hT') t ht ht' x
  let v := Q.compare n (Q.representativeIndex T) t.1 ht
    (Q.globalEventPreTime T hT' ⟨t.1, ht'⟩) (((Q.flow n).event T hT).pre_identify t x)
  have hs : (Q.globalEventSource T hT').pre_identify ⟨t.1, ht'⟩ y = v :=
    ((Q.globalEventSource T hT').pre_identify ⟨t.1, ht'⟩).apply_symm_apply v
  have hpoint : (Q.globalEvent T hT').pre_identify ⟨t.1, ht'⟩
      (Q.globalEventInitialMap T hT' y) =
      Q.globalIdentify n t.1 ht (((Q.flow n).event T hT).pre_identify t x) := by
    calc
      _ = Q.globalEventPreMap T hT' ⟨t.1, ht'⟩
          ((Q.globalEventSource T hT').pre_identify ⟨t.1, ht'⟩
            ((Q.globalEventInitialMap T hT').symm (Q.globalEventInitialMap T hT' y))) :=
        Q.globalEvent_pre_identify T hT' ⟨t.1, ht'⟩ _
      _ = Q.globalEventPreMap T hT' ⟨t.1, ht'⟩
          ((Q.globalEventSource T hT').pre_identify ⟨t.1, ht'⟩ y) :=
        congrArg (fun z => Q.globalEventPreMap T hT' ⟨t.1, ht'⟩
          ((Q.globalEventSource T hT').pre_identify ⟨t.1, ht'⟩ z))
            ((Q.globalEventInitialMap T hT').symm_apply_apply y)
      _ = Q.globalEventPreMap T hT' ⟨t.1, ht'⟩ v :=
        congrArg (Q.globalEventPreMap T hT' ⟨t.1, ht'⟩) hs
      _ = _ := Q.globalIdentify_compare n (Q.representativeIndex T) t.1 ht
        (Q.globalEventPreTime T hT' ⟨t.1, ht'⟩) _
  exact (congrArg ((Q.globalEvent T hT').pre_identify ⟨t.1, ht'⟩).symm hpoint).symm.trans
    (((Q.globalEvent T hT').pre_identify ⟨t.1, ht'⟩).symm_apply_apply _)

theorem globalEvent_old_retained_pre (n : ℕ) (T : ℝ)
    (hT : T ∈ (Q.flow n).surgery_times) (hT' : T ∈ Q.globalSurgeryTimes)
    [Nonempty ((Q.flow n).slice T).carrier] [Nonempty (Q.globalSlice T).carrier]
    (t : Ico ((Q.flow n).event T hT).tMinus T) (ht : t.1 ∈ (Q.flow n).time_domain)
    (ht' : t.1 ∈ Ico (Q.globalEvent T hT').tMinus T) :
    (fun x => ((Q.globalEvent T hT').pre_identify ⟨t.1, ht'⟩).symm
      (Q.globalIdentify n t.1 ht (((Q.flow n).event T hT).pre_identify t x))) ''
        ((Q.flow n).event T hT).retained_pre = (Q.globalEvent T hT').retained_pre := by
  let := Q.eventStageNonempty T hT'
  rw [Q.globalEvent_retained_pre]
  calc
    _ = (fun x => Q.globalEventInitialMap T hT'
        (Q.stageEventPreCompare n (Q.representativeIndex T) T hT
          (Q.eventStageSurgery T hT') t ht ht' x)) ''
        ((Q.flow n).event T hT).retained_pre := by
      congr 1
      funext x
      exact Q.globalEvent_pre_coordinate n T hT hT' t ht ht' x
    _ = Q.globalEventInitialMap T hT' ''
        (Q.stageEventPreCompare n (Q.representativeIndex T) T hT
          (Q.eventStageSurgery T hT') t ht ht' ''
            ((Q.flow n).event T hT).retained_pre) := (Set.image_image _ _ _).symm
    _ = _ := congrArg (fun A => Q.globalEventInitialMap T hT' '' A)
      (Q.stageEvent_retained_pre n (Q.representativeIndex T) T hT
        (Q.eventStageSurgery T hT') t ht ht')

theorem globalEvent_old_retention (n : ℕ) (T : ℝ)
    (hT : T ∈ (Q.flow n).surgery_times) (hT' : T ∈ Q.globalSurgeryTimes)
    [Nonempty ((Q.flow n).slice T).carrier] [Nonempty (Q.globalSlice T).carrier]
    (t : Ico ((Q.flow n).event T hT).tMinus T) (ht : t.1 ∈ (Q.flow n).time_domain)
    (ht' : t.1 ∈ Ico (Q.globalEvent T hT').tMinus T)
    (x : ((Q.flow n).slice ((Q.flow n).event T hT).tMinus).carrier)
    (hx : x ∈ ((Q.flow n).event T hT).retained_pre) :
    Q.globalIdentify n T ((Q.flow n).surgery_times_subset hT)
      (((Q.flow n).event T hT).retention.map x) =
        (Q.globalEvent T hT').retention.map
          (((Q.globalEvent T hT').pre_identify ⟨t.1, ht'⟩).symm
            (Q.globalIdentify n t.1 ht (((Q.flow n).event T hT).pre_identify t x))) := by
  let := Q.eventStageNonempty T hT'
  rw [Q.globalEvent_pre_coordinate, Q.globalEvent_retention_map,
    Diffeomorph.symm_apply_apply]
  calc
    _ = Q.globalEventPostMap T hT'
        (Q.compare n (Q.representativeIndex T) T ((Q.flow n).surgery_times_subset hT)
          (Q.eventStageTime T hT') (((Q.flow n).event T hT).retention.map x)) :=
      (Q.globalIdentify_compare n (Q.representativeIndex T) T
        ((Q.flow n).surgery_times_subset hT) (Q.eventStageTime T hT') _).symm
    _ = _ := congrArg (Q.globalEventPostMap T hT')
      (Q.stageEvent_retention n (Q.representativeIndex T) T hT
        (Q.eventStageSurgery T hT') t ht ht' x hx)

end PoincareConjecture.M51.CompletedStageChain
