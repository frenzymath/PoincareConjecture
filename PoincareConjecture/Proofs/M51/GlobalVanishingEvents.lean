import PoincareConjecture.Proofs.M51.GlobalEvents

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.M51.CompletedStageChain

variable {S : RepairedControlledSchedulesData.{u}}
  {N : RepairedNoncollapseInductionData S}
  {C : RepairedCanonicalInductionData S N}
  {F0 : SurgeryFlowData.{u}} {k : ℕ}
  (Q : CompletedStageChain S N C F0 k)

noncomputable def globalVanishingSource (T : ℝ) (hT : T ∈ Q.globalSurgeryTimes)
    [IsEmpty (Q.globalSlice T).carrier] :
    SurgeryVanishingEventData (Q.flow (Q.representativeIndex T)).parameters
      (Q.flow (Q.representativeIndex T)).slice
      (Q.flow (Q.representativeIndex T)).metric T := by
  letI := Q.eventStageIsEmpty T hT
  exact (Q.flow (Q.representativeIndex T)).vanishing_event T
    (Q.eventStageSurgery T hT)

theorem globalVanishingPreTime (T : ℝ) (hT : T ∈ Q.globalSurgeryTimes)
    [IsEmpty (Q.globalSlice T).carrier]
    (t : Set.Ico (Q.globalVanishingSource T hT).tMinus T) :
    t.1 ∈ (Q.flow (Q.representativeIndex T)).time_domain := by
  let := Q.eventStageIsEmpty T hT
  exact (Q.flow (Q.representativeIndex T)).vanishingEventPreInterval T
    (Q.eventStageSurgery T hT) t.2

noncomputable def globalVanishingPreMap (T : ℝ) (hT : T ∈ Q.globalSurgeryTimes)
    [IsEmpty (Q.globalSlice T).carrier]
    (t : Set.Ico (Q.globalVanishingSource T hT).tMinus T) :
    Diffeomorph (𝓡 3) (𝓡 3)
      ((Q.flow (Q.representativeIndex T)).slice t.1).carrier
      (Q.globalSlice t.1).carrier ∞ :=
  Q.globalIdentify _ t.1 (Q.globalVanishingPreTime T hT t)

noncomputable def globalVanishingInitialMap (T : ℝ) (hT : T ∈ Q.globalSurgeryTimes)
    [IsEmpty (Q.globalSlice T).carrier] :
    Diffeomorph (𝓡 3) (𝓡 3)
      ((Q.flow (Q.representativeIndex T)).slice
        (Q.globalVanishingSource T hT).tMinus).carrier
      (Q.globalSlice (Q.globalVanishingSource T hT).tMinus).carrier ∞ :=
  Q.globalVanishingPreMap T hT
    ⟨(Q.globalVanishingSource T hT).tMinus, le_rfl,
      (Q.globalVanishingSource T hT).tMinus_lt⟩

noncomputable def globalVanishingPullbackData
    (T : ℝ) (hT : T ∈ Q.globalSurgeryTimes) [IsEmpty (Q.globalSlice T).carrier] :
    SurgeryVanishingEventData.PullbackData (Q.globalVanishingSource T hT)
      Q.globalSlice Q.globalMetric (Q.globalVanishingInitialMap T hT).symm where
  sliceMap := Q.globalVanishingPreMap T hT
  initial_sliceMap := (Q.globalVanishingInitialMap T hT).apply_symm_apply
  slice_isometry t x v w :=
    Q.globalIdentify_metric _ t.1 (Q.globalVanishingPreTime T hT t) x v w

noncomputable def globalVanishingTransport
    (m13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (T : ℝ) (hT : T ∈ Q.globalSurgeryTimes) [IsEmpty (Q.globalSlice T).carrier] :
    SurgeryVanishingEventData (Q.flow (Q.representativeIndex T)).parameters
      Q.globalSlice Q.globalMetric T :=
  SurgeryVanishingEventData.PullbackData.toEvent m13
    (Q.globalVanishingSource T hT) (Q.globalVanishingPullbackData T hT)

noncomputable def globalVanishingEvent
    (m13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (T : ℝ) (hT : T ∈ Q.globalSurgeryTimes) [IsEmpty (Q.globalSlice T).carrier] :
    SurgeryVanishingEventData F0.parameters Q.globalSlice Q.globalMetric T :=
  (Q.globalVanishingTransport m13 T hT).castParameters (Q.parameters_eq _)

variable (m13 : GeneralizedParabolicRescalingTheory.{u} 3)
  (T : ℝ) (hT : T ∈ Q.globalSurgeryTimes) [IsEmpty (Q.globalSlice T).carrier]

@[simp] theorem globalVanishingEvent_tMinus :
    (Q.globalVanishingEvent m13 T hT).tMinus =
      (Q.globalVanishingSource T hT).tMinus := rfl

@[simp] theorem globalVanishingEvent_disappearing_start :
    (Q.globalVanishingEvent m13 T hT).disappearing_start =
      (Q.globalVanishingSource T hT).disappearing_start := rfl

@[simp] theorem globalVanishingEvent_left_limit_volume :
    (Q.globalVanishingEvent m13 T hT).left_limit_volume =
      (Q.globalVanishingSource T hT).left_limit_volume := rfl

@[simp] theorem globalVanishingEvent_pre_identify
    (t : Set.Ico (Q.globalVanishingSource T hT).tMinus T)
    (x : (Q.globalSlice (Q.globalVanishingSource T hT).tMinus).carrier) :
    (Q.globalVanishingEvent m13 T hT).pre_identify t x =
      Q.globalVanishingPreMap T hT t
        ((Q.globalVanishingSource T hT).pre_identify t
          ((Q.globalVanishingInitialMap T hT).symm x)) := rfl

theorem globalVanishingEvent_pre_metric_homothety (t : ℝ) :
    MetricHomothety ((Q.globalVanishingEvent m13 T hT).pre_flow.metric t)
      ((Q.globalVanishingSource T hT).pre_flow.metric t)
      (Q.globalVanishingInitialMap T hT).symm 1 :=
  SurgeryVanishingEventData.PullbackData.toEvent_pre_metric_homothety m13
    (Q.globalVanishingSource T hT) (Q.globalVanishingPullbackData T hT) t

theorem globalVanishingEvent_policy :
    SurgeryVanishingEventTerminalPolicy (Q.globalVanishingEvent m13 T hT) := by
  apply SurgeryVanishingEventData.castParameters_policy
  apply SurgeryVanishingEventData.PullbackData.toEvent_terminalPolicy
  let := Q.eventStageIsEmpty T hT
  exact (Q.terminal_policy (Q.representativeIndex T)).vanishing T
    (Q.eventStageTime T hT) (Q.eventStageSurgery T hT)

end PoincareConjecture.M51.CompletedStageChain
