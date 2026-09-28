import PoincareConjecture.Definitions.Ch15.SurgeryContinuation
import PoincareConjecture.Definitions.Ch15.SurgeryEndPolicy
import PoincareConjecture.Definitions.M32HornSelection
import PoincareConjecture.Definitions.M33EventPreservation
import PoincareConjecture.Statements.M25NeckCapTopology










set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture


theorem m33BoxIntervalSubset (G : GeneralizedRicciFlowData.{u}) (b : G.box_index) :
    (G.box b).interval ⊆ G.interval := by
  obtain ⟨U, _, hU⟩ := (G.box b).relatively_open
  rw [hU]
  exact Set.inter_subset_left





structure M33RegularHistoryRealization
    (G : GeneralizedRicciFlowData.{u}) (F : SurgeryFlowData.{u}) where
  time_subset : G.interval ⊆ F.time_domain
  forward : ∀ t : ℝ, t ∈ G.interval → (G.slice t).carrier → (F.slice t).carrier
  inverse : ∀ t : ℝ, t ∈ G.interval → (F.slice t).carrier → (G.slice t).carrier
  forward_openEmbedding : ∀ t ht, Topology.IsOpenEmbedding (forward t ht)
  forward_smooth : ∀ t ht, ContMDiff (𝓡 3) (𝓡 3) ∞ (forward t ht)
  inverse_smooth : ∀ t ht,
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (inverse t ht) (Set.range (forward t ht))
  left_inverse : ∀ t ht, Function.LeftInverse (inverse t ht) (forward t ht)
  right_inverse : ∀ t ht,
    Set.LeftInvOn (forward t ht) (inverse t ht) (Set.range (forward t ht))
  metric_pullback : ∀ t ht x v w,
    (F.metric t).inner (forward t ht x)
      (mfderiv (𝓡 3) (𝓡 3) (forward t ht) x v)
      (mfderiv (𝓡 3) (𝓡 3) (forward t ht) x w) =
        (G.metric t).inner x v w
  slab_compatibility : ∀ q a b hab hJ habs,
    ∀ s t : ℝ, ∀ hs : s ∈ Set.Icc a b, ∀ ht : t ∈ Set.Icc a b,
    ∀ hs' : s ∈ (G.box q).interval, ∀ ht' : t ∈ (G.box q).interval,
    ∀ x : (G.box q).carrier.carrier,
      (F.regular_slabs a b hab hJ habs).transport ⟨s, hs⟩ ⟨t, ht⟩
        (forward s (m33BoxIntervalSubset G q hs') ((G.box q).forward s hs' x)) =
      forward t (m33BoxIntervalSubset G q ht') ((G.box q).forward t ht' x)
  retained_at_surgery : ∀ q t (ht : t ∈ (G.box q).interval),
    ∀ (hT : t ∈ F.surgery_times) [Nonempty (F.slice t).carrier],
      (∃ s ∈ (G.box q).interval, s < t) → ∀ x : (G.box q).carrier.carrier,
        forward t (m33BoxIntervalSubset G q ht) ((G.box q).forward t ht x) ∈
          interior (F.event t hT).retained_post
  pre_retained_at_surgery : ∀ q t (_ht : t ∈ (G.box q).interval),
    ∀ (hT : t ∈ F.surgery_times) [Nonempty (F.slice t).carrier],
    ∀ s (hs : s ∈ (G.box q).interval),
    ∀ hs' : s ∈ Set.Ico (F.event t hT).tMinus t,
    ∀ x : (G.box q).carrier.carrier,
      ((F.event t hT).pre_identify ⟨s, hs'⟩).symm
        (forward s (m33BoxIntervalSubset G q hs) ((G.box q).forward s hs x)) ∈
          interior (F.event t hT).retained_pre
  surgery_compatibility : ∀ q t (ht : t ∈ (G.box q).interval),
    ∀ (hT : t ∈ F.surgery_times) [Nonempty (F.slice t).carrier],
    ∀ s (hs : s ∈ (G.box q).interval),
    ∀ hs' : s ∈ Set.Ico (F.event t hT).tMinus t,
    ∀ x : (G.box q).carrier.carrier,
      (F.event t hT).retention.map
        (((F.event t hT).pre_identify ⟨s, hs'⟩).symm
          (forward s (m33BoxIntervalSubset G q hs) ((G.box q).forward s hs x))) =
        forward t (m33BoxIntervalSubset G q ht) ((G.box q).forward t ht x)

structure RepairedPreterminalSlab (F : SurgeryFlowData.{u}) (T : ℝ) where
  start : ℝ
  start_mem : start ∈ F.time_domain
  start_lt : start < T
  start_initial_or_surgery : start = 0 ∨ start ∈ F.surgery_times
  time_subset : Set.Ico start T ⊆ F.time_domain
  surgery_free : Disjoint F.surgery_times (Set.Ioo start T)
  flow : RicciFlow 3 (F.slice start).carrier (Set.Ico start T)
  identify : ∀ t : Set.Ico start T,
    Diffeomorph (𝓡 3) (𝓡 3) (F.slice start).carrier (F.slice t.1).carrier ∞
  initial_identify : ∀ x, identify ⟨start, ⟨le_rfl, start_lt⟩⟩ x = x
  metric_pullback : ∀ t x v w,
    (F.metric t.1).inner (identify t x)
      (mfderiv (𝓡 3) (𝓡 3) (identify t) x v)
      (mfderiv (𝓡 3) (𝓡 3) (identify t) x w) =
        (flow.metric t.1).inner x v w
  transport_compatibility : ∀ a b hab hJ habs,
    ∀ s t : ℝ, ∀ hs : s ∈ Set.Icc a b, ∀ ht : t ∈ Set.Icc a b,
    ∀ hs' : s ∈ Set.Ico start T, ∀ ht' : t ∈ Set.Ico start T, ∀ x,
      (F.regular_slabs a b hab hJ habs).transport ⟨s, hs⟩ ⟨t, ht⟩
        (identify ⟨s, hs'⟩ x) = identify ⟨t, ht'⟩ x
  curvature_unbounded : ∀ L : ℝ, ∀ s : ℝ, s < T →
    ∃ t ∈ Set.Ioo (max start s) T, ∃ x : (F.slice start).carrier,
      L < (flow.connection t).curvatureTensorNorm x

inductive RepairedTerminalCoreStatus (X : Type u) (core : Set X) : Prop where
  | nonempty : core.Nonempty → RepairedTerminalCoreStatus X core
  | empty : core = ∅ → RepairedTerminalCoreStatus X core

structure RepairedContinuationInput (F : SurgeryFlowData.{u}) (T : ℝ) where
  terminal_pos : 0 < T
  time_domain_eq : F.time_domain = Set.Ico 0 T
  last_slab : RepairedPreterminalSlab F T
  admissible : SurgeryFlowAdmissible F
  pinched : SurgeryFlowPinched F
  canonical : SurgeryCanonicalAssumption F
  noncollapsed : SurgeryNoncollapsed F
  rho : ℝ
  rho_eq : rho = F.parameters.delta T * F.parameters.r T
  rho_pos : 0 < rho
  rho_lt_r : rho < F.parameters.r T
  r₀ : ℝ
  r₀_pos : 0 < r₀
  rho_lt_r₀ : rho < r₀
  controlled_core : Set (F.slice last_slab.start).carrier
  core_status : RepairedTerminalCoreStatus (F.slice last_slab.start).carrier controlled_core

  terminal_delta_bound : F.parameters.delta T ≤ F.local_constants.delta₀


  terminal_height_bound : F.parameters.h T ≤ F.local_constants.R₀ ^ (-1 / 2 : ℝ)
  terminal_height_rho_delta : F.parameters.h T ≤ rho * F.parameters.delta T
  terminal_height_rho_constant : F.parameters.h T ≤ rho / (2 * F.parameters.C)

structure RepairedContinuationLimitBridge
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M]
    {G : GeneralizedRicciFlowData.{u}} {T : ℝ}
    (H : SingularTimeAssumptions G T M)
    (L : RepairedSingularRegularLimitData H)
    (N : RepairedHornSelectionData H)
    {F : SurgeryFlowData.{u}} (I : RepairedContinuationInput F T) where

  appendixA : RepairedNeckCapTopologyTheory.{u}
  appendixA_accuracy : terminalAccuracyFactor * H.epsilon ≤ appendixA.epsilon₀
  constant_one_le : 1 ≤ H.constant
  history : M33RegularHistoryRealization G F


  reference_start_lt : I.last_slab.start < H.reference.tMinus
  reference_identify : ∀ t : Set.Ico H.reference.tMinus T,
    Diffeomorph (𝓡 3) (𝓡 3) (F.slice t.1).carrier M ∞
  history_reference : ∀ t : Set.Ico H.reference.tMinus T, ∀ x : M,
    history.forward t.1 (H.reference.window_subset t.2)
      (H.reference.forward t.1 t.2 x) = (reference_identify t).symm x
  reference_metric_pullback : ∀ t x v w,
    let s : Set.Ico I.last_slab.start T :=
      ⟨t.1, reference_start_lt.le.trans t.2.1, t.2.2⟩
    (H.reference.flow.metric t.1).inner
        (reference_identify t (I.last_slab.identify s x))
      (mfderiv (𝓡 3) (𝓡 3) (reference_identify t)
        (I.last_slab.identify s x)
        (mfderiv (𝓡 3) (𝓡 3) (I.last_slab.identify s) x v))
      (mfderiv (𝓡 3) (𝓡 3) (reference_identify t)
        (I.last_slab.identify s x)
        (mfderiv (𝓡 3) (𝓡 3) (I.last_slab.identify s) x w)) =
        (I.last_slab.flow.metric t.1).inner x v w
  reference_scalar_pullback : ∀ t x,
    let s : Set.Ico I.last_slab.start T :=
      ⟨t.1, reference_start_lt.le.trans t.2.1, t.2.2⟩
    (H.reference.flow.connection t.1).scalarCurvature
        (reference_identify t (I.last_slab.identify s x)) =
      (I.last_slab.flow.connection t.1).scalarCurvature x
  reference_transport_compatibility : ∀ a b hab hJ habs,
    ∀ s t : ℝ, ∀ hs : s ∈ Set.Icc a b, ∀ ht : t ∈ Set.Icc a b,
    ∀ hs' : s ∈ Set.Ico H.reference.tMinus T,
    ∀ ht' : t ∈ Set.Ico H.reference.tMinus T,
    ∀ x : (F.slice s).carrier,
      reference_identify ⟨t, ht'⟩
          ((F.regular_slabs a b hab hJ habs).transport
            ⟨s, hs⟩ ⟨t, ht⟩ x) = reference_identify ⟨s, hs'⟩ x
  limit_extension_eq : N.limit.extension = L.extension
  rho_lt_r₀ : I.rho < H.r₀
  core_map : (F.slice I.last_slab.start).carrier → M
  core_map_eq_reference : ∀ x,
    core_map x = reference_identify
      ⟨H.reference.tMinus, ⟨le_rfl, H.reference.tMinus_lt⟩⟩
      (I.last_slab.identify
        ⟨H.reference.tMinus, reference_start_lt.le, H.reference.tMinus_lt⟩ x)
  core_map_image : core_map '' I.controlled_core =
    {y | y ∈ H.reference.regularLimitSet ∧
      ∃ z : (N.limit.extension.extended.slice T).carrier,
        N.limit.terminal_source z = y ∧
          N.limit.terminal_scalar z ≤ I.rho⁻¹ ^ 2}
  core_status_iff : I.controlled_core.Nonempty ↔
    (∃ y ∈ H.reference.regularLimitSet,
      ∃ z : (N.limit.extension.extended.slice T).carrier,
        N.limit.terminal_source z = y ∧
          N.limit.terminal_scalar z ≤ I.rho⁻¹ ^ 2)
  parameter_epsilon_eq : H.epsilon = F.parameters.epsilon
  parameter_constant_eq : H.constant = F.parameters.C
  parameter_r₀_eq : H.r₀ = I.r₀


  surgery_operation :
    ∀ J : MetricSurgeryInput F.local_constants (N.limit.extension.extended.metric T),
      Nonempty (MetricSurgeryResult F.standard_initial J)


  deep_horn_application :
    ∀ (horn : StrongHorn N.limit.extension (terminalAccuracyFactor * H.epsilon)),
    HornBoundaryBelow horn (I.rho / (2 * H.constant)) →
      Nonempty (DeepHornNeckConclusion N.limit.extension
        (terminalAccuracyFactor * H.epsilon) H.constant I.rho (F.parameters.delta T)
        horn (F.parameters.h T))

structure RepairedNonemptyTerminalOperationCertificate
    {F : SurgeryFlowData.{u}} {T : ℝ}
    (I : RepairedContinuationInput F T)
    (E : SurgeryFlowExtension F)
    (hT : T ∈ E.extended.surgery_times)
    (hpost : Nonempty (E.extended.slice T).carrier) where
  reference_time : ℝ
  reference_mem : reference_time ∈ Set.Ico I.last_slab.start T
  reference_h : ℝ
  reference_h_pos : 0 < reference_h
  reference_h_eq : reference_h = F.parameters.h T
  reference_close : T - reference_h ^ 2 < reference_time
  event : SurgeryEventData E.extended.standard_initial E.extended.local_constants
    E.extended.parameters E.extended.slice E.extended.metric T
  event_eq : event = E.extended.event T hT
  terminal_policy : SurgeryEventTerminalPolicy event
  event_tMinus_mem : event.tMinus ∈ F.time_domain
  event_tMinus_slab_mem : event.tMinus ∈ Set.Ico I.last_slab.start T
  event_tMinus_eq_reference :
    event.tMinus = reference_time
  reference_identify : Diffeomorph (𝓡 3) (𝓡 3)
    (F.slice I.last_slab.start).carrier
    (E.extended.slice reference_time).carrier ∞
  reference_identify_eq : ∀ x,
      reference_identify x =
      E.identify reference_time
        (I.last_slab.time_subset reference_mem)
        (I.last_slab.identify ⟨reference_time, reference_mem⟩ x)
  retained_post : Set (E.extended.slice T).carrier
  retained_post_eq : retained_post = event.retained_post
  core_nonempty : I.controlled_core.Nonempty
  source_to_pre : Diffeomorph (𝓡 3) (𝓡 3)
    (F.slice I.last_slab.start).carrier
    (E.extended.slice event.tMinus).carrier ∞
  source_to_pre_eq : ∀ x, source_to_pre x =
    E.identify event.tMinus event_tMinus_mem
      (I.last_slab.identify ⟨event.tMinus, event_tMinus_slab_mem⟩ x)
  reference_identify_eq_source : ∀ x,
    reference_identify x =
      cast (by rw [event_tMinus_eq_reference]) (source_to_pre x)
  pre_identify_transport : ∀ (t : Set.Ico event.tMinus T)
    (htF : t.1 ∈ F.time_domain) (htS : t.1 ∈ Set.Ico I.last_slab.start T) x,
    event.pre_identify t (source_to_pre x) =
      E.identify t.1 htF
        (I.last_slab.identify ⟨t.1, htS⟩ x)
  regular_limit_source : Set (F.slice I.last_slab.start).carrier
  regular_limit_transport : event.regular_limit = source_to_pre '' regular_limit_source
  controlled_core_subset_regular_limit : I.controlled_core ⊆ regular_limit_source
  controlled_core_threshold : ∀ x ∈ I.controlled_core,
    event.limit_connection.scalarCurvature
      (event.limit_identify.map (source_to_pre x)) ≤ I.rho⁻¹ ^ 2
  pre_flow_metric_transport : ∀ (t : Set.Ico event.tMinus T) x v w,
    (event.pre_flow.metric t).inner
        (source_to_pre x)
        (mfderiv (𝓡 3) (𝓡 3) source_to_pre x v)
        (mfderiv (𝓡 3) (𝓡 3) source_to_pre x w) =
      (I.last_slab.flow.metric t).inner
        x v w
  disappearing_cover_rebased : ∀ (t : Set.Ico event.disappearing_start T) x,
      source_to_pre x ∉ interior event.retained_pre →
      (∃ N : EpsilonNeck (event.pre_flow.metric t),
        N.center = source_to_pre x ∧ N.epsilon = E.extended.parameters.epsilon) ∨
      (∃ N : CapCertificate (event.pre_flow.metric t),
        source_to_pre x ∈ N.core ∧ N.epsilon = E.extended.parameters.epsilon ∧
          N.cap_constant ≤ E.extended.parameters.C) ∨
      (∃ U : Set (E.extended.slice event.tMinus).carrier,
        source_to_pre x ∈ U ∧ U = connectedComponent (source_to_pre x) ∧
        ∀ y ∈ U, ∀ v w : TangentSpace (𝓡 3) y,
          LeviCivitaData.IsOrthonormalPair (event.pre_flow.metric t) y v w →
            0 < (event.pre_flow.connection t).sectionalCurvature y v w)

structure RepairedVanishingTerminalOperationCertificate
    {F : SurgeryFlowData.{u}} {T : ℝ}
    (I : RepairedContinuationInput F T)
    (E : SurgeryFlowExtension F)
    (hT : T ∈ E.extended.surgery_times)
    (hempty : IsEmpty (E.extended.slice T).carrier) where
  reference_time : ℝ
  reference_mem : reference_time ∈ Set.Ico I.last_slab.start T
  reference_h : ℝ
  reference_h_pos : 0 < reference_h
  reference_h_eq : reference_h = F.parameters.h T
  reference_close : T - reference_h ^ 2 < reference_time
  event : SurgeryVanishingEventData E.extended.parameters E.extended.slice
    E.extended.metric T
  event_eq : event = E.extended.vanishing_event T hT
  terminal_policy : SurgeryVanishingEventTerminalPolicy event
  event_tMinus_mem : event.tMinus ∈ F.time_domain
  event_tMinus_slab_mem : event.tMinus ∈ Set.Ico I.last_slab.start T
  event_tMinus_eq_reference :
    event.tMinus = reference_time
  reference_identify : Diffeomorph (𝓡 3) (𝓡 3)
    (F.slice I.last_slab.start).carrier
    (E.extended.slice reference_time).carrier ∞
  reference_identify_eq : ∀ x,
      reference_identify x =
      E.identify reference_time
        (I.last_slab.time_subset reference_mem)
        (I.last_slab.identify ⟨reference_time, reference_mem⟩ x)
  core_empty : I.controlled_core = ∅
  source_to_pre : Diffeomorph (𝓡 3) (𝓡 3)
    (F.slice I.last_slab.start).carrier
    (E.extended.slice event.tMinus).carrier ∞
  source_to_pre_eq : ∀ x, source_to_pre x =
    E.identify event.tMinus event_tMinus_mem
      (I.last_slab.identify ⟨event.tMinus, event_tMinus_slab_mem⟩ x)
  reference_identify_eq_source : ∀ x,
    reference_identify x =
      cast (by rw [event_tMinus_eq_reference]) (source_to_pre x)
  pre_identify_transport : ∀ (t : Set.Ico event.tMinus T)
    (htF : t.1 ∈ F.time_domain) (htS : t.1 ∈ Set.Ico I.last_slab.start T) x,
    event.pre_identify t (source_to_pre x) =
      E.identify t.1 htF
        (I.last_slab.identify ⟨t.1, htS⟩ x)
  pre_flow_metric_transport : ∀ (t : Set.Ico event.tMinus T) x v w,
    (event.pre_flow.metric t).inner
        (source_to_pre x)
        (mfderiv (𝓡 3) (𝓡 3) source_to_pre x v)
        (mfderiv (𝓡 3) (𝓡 3) source_to_pre x w) =
      (I.last_slab.flow.metric t).inner
        x v w
  disappearing_cover_rebased : ∀ (t : Set.Ico event.disappearing_start T) x,
    (∃ N : EpsilonNeck (event.pre_flow.metric t),
      N.center = source_to_pre x ∧ N.epsilon = E.extended.parameters.epsilon) ∨
    (∃ N : CapCertificate (event.pre_flow.metric t),
      source_to_pre x ∈ N.core ∧ N.epsilon = E.extended.parameters.epsilon ∧
        N.cap_constant ≤ E.extended.parameters.C) ∨
    (∃ U : Set (E.extended.slice event.tMinus).carrier,
      source_to_pre x ∈ U ∧ U = connectedComponent (source_to_pre x) ∧
      ∀ y ∈ U, ∀ v w : TangentSpace (𝓡 3) y,
        LeviCivitaData.IsOrthonormalPair (event.pre_flow.metric t) y v w →
          0 < (event.pre_flow.connection t).sectionalCurvature y v w)
  no_later_surgery : ∀ s, T < s → s ∈ E.extended.time_domain →
    s ∉ E.extended.surgery_times

inductive RepairedTerminalOperation
    {F : SurgeryFlowData.{u}} {T : ℝ}
    (I : RepairedContinuationInput F T)
    (E : SurgeryFlowExtension F)
    (hT : T ∈ E.extended.surgery_times) where
  | nonempty (hpost : Nonempty (E.extended.slice T).carrier)
      (operation : RepairedNonemptyTerminalOperationCertificate I E hT hpost)
  | vanishing (hempty : IsEmpty (E.extended.slice T).carrier)
      (operation : RepairedVanishingTerminalOperationCertificate I E hT hempty)

structure RepairedContinuationConclusion
    {F : SurgeryFlowData.{u}} {T : ℝ}
    (I : RepairedContinuationInput F T) where
  extension : SurgeryFlowExtension F


  old_event_data : M33OldEventDataPreservation extension
  end_time : ℝ≥0∞
  extends_past : ENNReal.ofReal T < end_time
  time_domain_eq : extension.extended.time_domain =
    {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < end_time}
  surgery_at_terminal : T ∈ extension.extended.surgery_times
  terminal_operation : RepairedTerminalOperation I extension surgery_at_terminal
  terminal_nonempty_iff : I.controlled_core.Nonempty ↔
    Nonempty (extension.extended.slice T).carrier
  terminal_empty_iff : I.controlled_core = ∅ ↔
    IsEmpty (extension.extended.slice T).carrier




  terminal_empty_end_time_top : I.controlled_core = ∅ → end_time = ⊤
  post_terminal_interval : ∃ d : ℝ, 0 < d ∧
    Set.Ioo T (T + d) ⊆ extension.extended.time_domain ∧
    Disjoint extension.extended.surgery_times (Set.Ioo T (T + d))
  admissible : SurgeryFlowAdmissible extension.extended
  pinched : SurgeryFlowPinched extension.extended
  extinction_permanent : ∀ s t : ℝ,
    s ∈ extension.extended.time_domain →
    t ∈ extension.extended.time_domain →
    s ≤ t →
    IsEmpty (extension.extended.slice s).carrier →
    IsEmpty (extension.extended.slice t).carrier


  no_later_surgery : ∀ t ∈ extension.extended.time_domain,
    T < t → t ∉ extension.extended.surgery_times
  finite_end_slab : end_time ≠ ⊤ →
    ∃ next : RepairedPreterminalSlab extension.extended end_time.toReal,
      next.start = T

structure RepairedBranchContinuationData
    {F : SurgeryFlowData.{u}} {T : ℝ}
    (I : RepairedContinuationInput F T) where
  conclusion : RepairedContinuationConclusion I

end PoincareConjecture
