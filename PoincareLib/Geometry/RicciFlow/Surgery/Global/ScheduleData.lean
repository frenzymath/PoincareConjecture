import PoincareLib.Geometry.RicciFlow.Surgery.Global.Certificate
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.NoncollapseGeometry
import PoincareLib.Geometry.RicciFlow.Surgery.Volume.FinitePrefixData
import PoincareLib.Geometry.RicciFlow.Surgery.Flow.TerminalPolicy

/-!
Adapted from Mapher `PoincareMT/Definitions/M51GlobalSchedule.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# M51 repaired global schedule induction data

This partial global certificate records the actual changing-carrier flow and
the schedule/finite-prefix information assembled before the stronger M52
controlled-flow certificate is formed.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-! Theorem 15.9 has two source-facing uses. Corollary 15.10 starts from a
normalized initial metric; Theorem 15.9 also extends an already given finite
controlled flow. Keep that second input primitive and tied to its actual flow
so the global theorem cannot replace it by a newly chosen solution. -/

structure RepairedGlobalControlledPrefix
    {K : MetricSurgeryConstants} (schedule : GlobalSurgerySchedule K)
    (delta : ℝ → ℝ) (flow : SurgeryFlowData.{u}) (horizon : ℝ) : Prop where
  horizon_pos : 0 < horizon
  time_domain_eq : flow.time_domain = Set.Ico 0 horizon
  local_constants_eq : flow.local_constants = K
  standard_initial_eq : flow.standard_initial = schedule.setup.standard_initial
  parameters_epsilon_eq : flow.parameters.epsilon = schedule.setup.epsilon
  parameters_C_eq : flow.parameters.C = schedule.setup.C
  admissible : SurgeryFlowAdmissible flow
  /-- The given history already uses the Definition 15.8 surgery policy. -/
  terminal_policy : SurgeryFlowTerminalPolicyOn flow flow.time_domain
  pinched : SurgeryFlowPinched flow
  canonical : SurgeryCanonicalAssumption flow
  noncollapsed : SurgeryNoncollapsed flow
  delta_eq : ∀ t, 0 ≤ t → flow.parameters.delta t = delta t
  /-- An extension preserves the entire parameter record. The numerical
      profiles are therefore prescribed on all nonnegative times; no future
      geometric control is an input. -/
  schedule_agreement : ∀ j : ℕ, ∀ t ∈ surgeryEpochEntry j,
    0 ≤ t →
      flow.parameters.r t = schedule.r j ∧
      flow.parameters.kappa t = schedule.kappa j ∧
      flow.parameters.h t = schedule.setup.selector.h
        (delta t * flow.parameters.r t) (delta t)

structure RepairedGlobalControlledExtension
    {K : MetricSurgeryConstants} (schedule : GlobalSurgerySchedule K)
    (flow : SurgeryFlowData.{u}) where
  extension : SurgeryFlowExtension flow
  time_domain_eq : extension.extended.time_domain = Set.Ici 0
  admissible : SurgeryFlowAdmissible extension.extended
  terminal_policy :
    SurgeryFlowTerminalPolicyOn extension.extended extension.extended.time_domain
  pinched : SurgeryFlowPinched extension.extended
  canonical : SurgeryCanonicalAssumption extension.extended
  noncollapsed : SurgeryNoncollapsed extension.extended
  schedule_agreement : ∀ j : ℕ, ∀ t ∈ surgeryEpochEntry j,
    t ∈ extension.extended.time_domain →
      extension.extended.parameters.r t = schedule.r j ∧
      extension.extended.parameters.kappa t = schedule.kappa j ∧
      extension.extended.parameters.delta t ≤ schedule.Delta j ∧
      extension.extended.parameters.h t = schedule.setup.selector.h
        (extension.extended.parameters.delta t * extension.extended.parameters.r t)
        (extension.extended.parameters.delta t)
  local_finite : ∀ Kset : Set ℝ, IsCompact Kset →
    (extension.extended.surgery_times ∩ Kset).Finite
  no_finite_accumulation : ∀ T : ℝ, T ∉ extension.extended.surgery_times →
    ∃ d : ℝ, 0 < d ∧
      (extension.extended.surgery_times ∩ Set.Ioo (T - d) (T + d)).Finite

structure RepairedGlobalScheduleData
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M]
    (N : NormalizedInitialMetric (M := M)) where
  flow : SurgeryFlowData.{u}
  schedule : GlobalSurgerySchedule flow.local_constants
  prefix_witness : ∀ i : ℕ, 0 < i →
    Nonempty (GlobalSurgeryPrefixWitness flow.local_constants schedule i)
  control_function : ℝ → ℝ
  control_antitone : AntitoneOn control_function (Set.Ici 0)
  control_positive : ∀ t ∈ flow.time_domain, 0 < control_function t
  control_eq : ∀ t ∈ flow.time_domain,
    flow.parameters.delta t = control_function t
  /-- The global flow keeps the setup's epsilon and cap constant. -/
  parameters_epsilon_eq : flow.parameters.epsilon = schedule.setup.epsilon
  parameters_C_eq : flow.parameters.C = schedule.setup.C
  /-- Whole-domain controls exported by the M48 extension chain. -/
  admissible : SurgeryFlowAdmissible flow
  /-- Constructed from the actual finite stages and their copied events. -/
  terminal_policy : SurgeryFlowTerminalPolicyOn flow flow.time_domain
  pinched : SurgeryFlowPinched flow
  canonical : SurgeryCanonicalAssumption flow
  noncollapsed : SurgeryNoncollapsed flow
  schedule_standard_initial : schedule.setup.standard_initial = flow.standard_initial
  /-- M51 applies M49 to this same raw flow after tightening the schedule
      below M49's selected cutoff. No selected M37 operation is required. -/
  volume_nonempty_pre_interval : RepairedNonemptyEventPreInterval flow
  volume_vanishing_pre_interval : RepairedVanishingEventPreInterval flow
  volume_zero_cap_discard : RepairedZeroCapDiscard flow
  volume_loss : RepairedVolumeLossData flow {
    admissible := admissible
    pinched := pinched
    nonempty_pre_interval := volume_nonempty_pre_interval
    vanishing_pre_interval := volume_vanishing_pre_interval
    zero_cap_discard := volume_zero_cap_discard }
  time_domain_eq : flow.time_domain = Set.Ici 0
  initial_identification : Diffeomorph (𝓡 3) (𝓡 3) M
    (flow.slice 0).carrier ∞
  initial_metric_pullback : ∀ x v w,
    (flow.metric 0).inner (initial_identification x)
      (mfderiv (𝓡 3) (𝓡 3) initial_identification x v)
      (mfderiv (𝓡 3) (𝓡 3) initial_identification x w) =
        N.metric.inner x v w
  schedule_agreement : ∀ j : ℕ, ∀ t ∈ surgeryEpochEntry j,
    t ∈ flow.time_domain →
      flow.parameters.r t = schedule.r j ∧
      flow.parameters.kappa t = schedule.kappa j ∧
      flow.parameters.delta t ≤ schedule.Delta j ∧
      flow.parameters.h t = schedule.setup.selector.h
        (flow.parameters.delta t * flow.parameters.r t)
        (flow.parameters.delta t)
  local_finite : ∀ Kset : Set ℝ, IsCompact Kset →
    (flow.surgery_times ∩ Kset).Finite

end PoincareMT
