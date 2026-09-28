import PoincareConjecture.Proofs.M51.GlobalRepresentatives
import PoincareConjecture.Proofs.M51.EventTransportMetadata
import PoincareConjecture.Proofs.M51.EventIntervals











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


theorem eventStageTime (T : ℝ) (hT : T ∈ Q.globalSurgeryTimes) :
    T ∈ (Q.flow (Q.representativeIndex T)).time_domain :=
  Q.representative_time T (Q.globalSurgeryTimes_nonnegative hT)


theorem eventStageSurgery (T : ℝ) (hT : T ∈ Q.globalSurgeryTimes) :
    T ∈ (Q.flow (Q.representativeIndex T)).surgery_times :=
  (Q.global_surgery_iff _ T (Q.eventStageTime T hT)).mp hT


noncomputable def globalEventPostMap (T : ℝ) (hT : T ∈ Q.globalSurgeryTimes) :
    Diffeomorph (𝓡 3) (𝓡 3)
      ((Q.flow (Q.representativeIndex T)).slice T).carrier
      (Q.globalSlice T).carrier ∞ :=
  Q.globalIdentify _ T (Q.eventStageTime T hT)


theorem eventStageNonempty (T : ℝ) (hT : T ∈ Q.globalSurgeryTimes)
    [Nonempty (Q.globalSlice T).carrier] :
    Nonempty ((Q.flow (Q.representativeIndex T)).slice T).carrier := by
  obtain ⟨x⟩ := ‹Nonempty (Q.globalSlice T).carrier›
  exact ⟨(Q.globalEventPostMap T hT).symm x⟩


theorem eventStageIsEmpty (T : ℝ) (hT : T ∈ Q.globalSurgeryTimes)
    [IsEmpty (Q.globalSlice T).carrier] :
    IsEmpty ((Q.flow (Q.representativeIndex T)).slice T).carrier :=
  ⟨fun x => isEmptyElim (Q.globalEventPostMap T hT x)⟩


noncomputable def globalEventSource (T : ℝ) (hT : T ∈ Q.globalSurgeryTimes)
    [Nonempty (Q.globalSlice T).carrier] :
    SurgeryEventData (Q.flow (Q.representativeIndex T)).standard_initial
      (Q.flow (Q.representativeIndex T)).local_constants
      (Q.flow (Q.representativeIndex T)).parameters
      (Q.flow (Q.representativeIndex T)).slice
      (Q.flow (Q.representativeIndex T)).metric T := by
  letI := Q.eventStageNonempty T hT
  exact (Q.flow (Q.representativeIndex T)).event T (Q.eventStageSurgery T hT)


theorem globalEventPreTime (T : ℝ) (hT : T ∈ Q.globalSurgeryTimes)
    [Nonempty (Q.globalSlice T).carrier]
    (t : Set.Ico (Q.globalEventSource T hT).tMinus T) :
    t.1 ∈ (Q.flow (Q.representativeIndex T)).time_domain := by
  let := Q.eventStageNonempty T hT
  exact (Q.flow (Q.representativeIndex T)).nonemptyEventPreInterval T
    (Q.eventStageSurgery T hT) t.2


noncomputable def globalEventPreMap (T : ℝ) (hT : T ∈ Q.globalSurgeryTimes)
    [Nonempty (Q.globalSlice T).carrier]
    (t : Set.Ico (Q.globalEventSource T hT).tMinus T) :
    Diffeomorph (𝓡 3) (𝓡 3)
      ((Q.flow (Q.representativeIndex T)).slice t.1).carrier
      (Q.globalSlice t.1).carrier ∞ :=
  Q.globalIdentify _ t.1 (Q.globalEventPreTime T hT t)


noncomputable def globalEventInitialMap (T : ℝ) (hT : T ∈ Q.globalSurgeryTimes)
    [Nonempty (Q.globalSlice T).carrier] :
    Diffeomorph (𝓡 3) (𝓡 3)
      ((Q.flow (Q.representativeIndex T)).slice
        (Q.globalEventSource T hT).tMinus).carrier
      (Q.globalSlice (Q.globalEventSource T hT).tMinus).carrier ∞ :=
  Q.globalEventPreMap T hT
    ⟨(Q.globalEventSource T hT).tMinus, le_rfl, (Q.globalEventSource T hT).tMinus_lt⟩


theorem globalEventPreMap_metric (T : ℝ) (hT : T ∈ Q.globalSurgeryTimes)
    [Nonempty (Q.globalSlice T).carrier]
    (t : Set.Ico (Q.globalEventSource T hT).tMinus T)
    (x : ((Q.flow (Q.representativeIndex T)).slice t.1).carrier)
    (v w : TangentSpace (𝓡 3) x) :
    (Q.globalMetric t.1).inner (Q.globalEventPreMap T hT t x)
      (mfderiv (𝓡 3) (𝓡 3) (Q.globalEventPreMap T hT t) x v)
      (mfderiv (𝓡 3) (𝓡 3) (Q.globalEventPreMap T hT t) x w) =
        ((Q.flow (Q.representativeIndex T)).metric t.1).inner x v w :=
  Q.globalIdentify_metric _ t.1 (Q.globalEventPreTime T hT t) x v w


theorem globalEventPostMap_metric (T : ℝ) (hT : T ∈ Q.globalSurgeryTimes)
    (x : ((Q.flow (Q.representativeIndex T)).slice T).carrier)
    (v w : TangentSpace (𝓡 3) x) :
    (Q.globalMetric T).inner (Q.globalEventPostMap T hT x)
      (mfderiv (𝓡 3) (𝓡 3) (Q.globalEventPostMap T hT) x v)
      (mfderiv (𝓡 3) (𝓡 3) (Q.globalEventPostMap T hT) x w) =
        ((Q.flow (Q.representativeIndex T)).metric T).inner x v w :=
  Q.globalIdentify_metric _ T (Q.eventStageTime T hT) x v w


noncomputable def globalEventTransport (T : ℝ) (hT : T ∈ Q.globalSurgeryTimes)
    [Nonempty (Q.globalSlice T).carrier] :
    SurgeryEventData (Q.flow (Q.representativeIndex T)).standard_initial
      (Q.flow (Q.representativeIndex T)).local_constants
      (Q.flow (Q.representativeIndex T)).parameters Q.globalSlice Q.globalMetric T :=
  (Q.globalEventSource T hT).transport (Q.globalEventPreMap T hT)
    (Q.globalEventPostMap T hT) (Q.globalEventPreMap_metric T hT)
    (Q.globalEventPostMap_metric T hT)
    (M51EventTransport.MetricLimitTransportData.of_source
      (slice' := Q.globalSlice) (Q.globalEventSource T hT) (Q.globalEventInitialMap T hT))


noncomputable def globalEvent (T : ℝ) (hT : T ∈ Q.globalSurgeryTimes)
    [Nonempty (Q.globalSlice T).carrier] :
    SurgeryEventData F0.standard_initial F0.local_constants F0.parameters
      Q.globalSlice Q.globalMetric T :=
  (Q.globalEventTransport T hT).castMetadata
    (Q.standard_initial_eq _) (Q.local_constants_eq _) (Q.parameters_eq _)

variable (T : ℝ) (hT : T ∈ Q.globalSurgeryTimes)
  [Nonempty (Q.globalSlice T).carrier]


@[simp] theorem globalEvent_tMinus :
    (Q.globalEvent T hT).tMinus = (Q.globalEventSource T hT).tMinus := rfl


@[simp] theorem globalEvent_terminal :
    (Q.globalEvent T hT).terminal = (Q.globalEventSource T hT).terminal := rfl


@[simp] theorem globalEvent_limit_metric :
    (Q.globalEvent T hT).limit_metric = (Q.globalEventSource T hT).limit_metric := rfl


@[simp] theorem globalEvent_limit_connection :
    (Q.globalEvent T hT).limit_connection =
      (Q.globalEventSource T hT).limit_connection := rfl


@[simp] theorem globalEvent_cap_count :
    (Q.globalEvent T hT).cap_count = (Q.globalEventSource T hT).cap_count := rfl


@[simp] theorem globalEvent_disappearing_start :
    (Q.globalEvent T hT).disappearing_start =
      (Q.globalEventSource T hT).disappearing_start := rfl


@[simp] theorem globalEvent_pre_flow :
    (Q.globalEvent T hT).pre_flow =
      (Q.globalEventSource T hT).pre_flow.pullbackDiffeomorph
        (Q.globalEventInitialMap T hT).symm := rfl


@[simp] theorem globalEvent_pre_identify
    (t : Set.Ico (Q.globalEventSource T hT).tMinus T)
    (x : (Q.globalSlice (Q.globalEventSource T hT).tMinus).carrier) :
    (Q.globalEvent T hT).pre_identify t x =
      Q.globalEventPreMap T hT t
        ((Q.globalEventSource T hT).pre_identify t
          ((Q.globalEventInitialMap T hT).symm x)) := rfl


@[simp] theorem globalEvent_limit_map
    (x : (Q.globalSlice (Q.globalEventSource T hT).tMinus).carrier) :
    (Q.globalEvent T hT).limit_identify.map x =
      (Q.globalEventSource T hT).limit_identify.map
        ((Q.globalEventInitialMap T hT).symm x) := rfl


@[simp] theorem globalEvent_limit_inverse
    (x : (Q.globalEventSource T hT).terminal.carrier) :
    (Q.globalEvent T hT).limit_identify.inverse x =
      Q.globalEventInitialMap T hT
        ((Q.globalEventSource T hT).limit_identify.inverse x) := rfl


@[simp] theorem globalEvent_retention_map
    (x : (Q.globalSlice (Q.globalEventSource T hT).tMinus).carrier) :
    (Q.globalEvent T hT).retention.map x =
      Q.globalEventPostMap T hT ((Q.globalEventSource T hT).retention.map
        ((Q.globalEventInitialMap T hT).symm x)) := rfl


theorem globalEvent_retained_pre :
    (Q.globalEvent T hT).retained_pre =
      Q.globalEventInitialMap T hT '' (Q.globalEventSource T hT).retained_pre :=
  ((Q.globalEventInitialMap T hT).image_eq_preimage_symm _).symm


theorem globalEvent_retained_post :
    (Q.globalEvent T hT).retained_post =
      Q.globalEventPostMap T hT '' (Q.globalEventSource T hT).retained_post :=
  ((Q.globalEventPostMap T hT).image_eq_preimage_symm _).symm


theorem globalEvent_necks :
    HEq (Q.globalEvent T hT).necks (Q.globalEventSource T hT).necks :=
  (Q.globalEventTransport T hT).castMetadata_necks
    (Q.standard_initial_eq _) (Q.local_constants_eq _) (Q.parameters_eq _)


@[simp] theorem globalEvent_neck (i : Fin (Q.globalEventSource T hT).cap_count) :
    ((Q.globalEvent T hT).necks i).neck = ((Q.globalEventSource T hT).necks i).neck := rfl


theorem globalEvent_local_result :
    HEq (Q.globalEvent T hT).local_result (Q.globalEventSource T hT).local_result :=
  (Q.globalEventTransport T hT).castMetadata_local_result
    (Q.standard_initial_eq _) (Q.local_constants_eq _) (Q.parameters_eq _)


theorem globalEvent_policy : Nonempty (SurgeryEventTerminalPolicy (Q.globalEvent T hT)) := by
  apply SurgeryEventData.castMetadata_policy
  apply SurgeryEventData.transport_policy
  let := Q.eventStageNonempty T hT
  exact (Q.terminal_policy (Q.representativeIndex T)).nonempty T
    (Q.eventStageTime T hT) (Q.eventStageSurgery T hT)

end PoincareConjecture.M51.CompletedStageChain
