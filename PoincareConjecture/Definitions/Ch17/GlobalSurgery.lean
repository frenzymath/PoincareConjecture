import PoincareConjecture.Definitions.Ch16.ControlledSurgery
import PoincareConjecture.Definitions.Ch15.SurgeryContinuation










set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

def NoTrivialNormalProjectivePlane {M : Type u} [TopologicalSpace M] : Prop :=
  ¬ ∃ f : RealProjectiveTwo × Set.Ioo (-1 : ℝ) 1 → M,
    Topology.IsOpenEmbedding f

structure GlobalSurgerySchedule (K : MetricSurgeryConstants) where
  setup : SurgeryControlSetup K
  epoch : ℕ → Set ℝ
  epoch_eq : ∀ j, epoch j = surgeryEpochEntry j
  r : ℕ → ℝ
  kappa : ℕ → ℝ
  Delta : ℕ → ℝ
  r_pos : ∀ j, 0 < r j
  kappa_pos : ∀ j, 0 < kappa j
  Delta_pos : ∀ j, 0 < Delta j
  r_antitone : Antitone r
  kappa_antitone : Antitone kappa
  Delta_antitone : Antitone Delta
  r_zero : r 0 = setup.epsilon
  r_le_epsilon : ∀ j, r j ≤ setup.epsilon


  kappa_zero_seed : ∃ κ₀ : ℝ, 0 < κ₀ ∧ kappa 0 = κ₀

  Delta_zero_seed : ∃ β δ₀' K₀ D₀ : ℝ,
    0 < β ∧ β < 1 / 2 ∧ 0 < δ₀' ∧ 0 < K₀ ∧ 0 < D₀ ∧
      Delta 0 = min (β * setup.epsilon / 3)
        (min δ₀' (min K₀⁻¹ D₀⁻¹))
  Delta_le : ∀ j, Delta j ≤ K.delta₀
  kappa_le : ∀ j, kappa (j + 1) ≤ kappa j
  overlap_bound : ∀ j, setup.selector.h
      (Delta (j + 1) * r (j + 1)) (Delta (j + 1)) ≤
    setup.selector.h (Delta j * r j) (Delta j)



structure GlobalSurgeryPrefixWitness (K : MetricSurgeryConstants)
    (S : GlobalSurgerySchedule K) (i : ℕ) where
  param_prefix : SurgeryParameterPrefix K
  prefix_index : param_prefix.i = i
  setup_eq : param_prefix.setup = S.setup
  prefix_agrees :
    (∀ j : Fin (i + 1), param_prefix.r
      (Fin.cast (congrArg Nat.succ prefix_index).symm j) = S.r j.val) ∧
    (∀ j : Fin (i + 1), param_prefix.kappa
      (Fin.cast (congrArg Nat.succ prefix_index).symm j) = S.kappa j.val) ∧
    (∀ j : Fin (i + 1), param_prefix.Delta
      (Fin.cast (congrArg Nat.succ prefix_index).symm j) = S.Delta j.val)

structure GlobalSurgeryFlowCertificate
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M]
    (N : NormalizedInitialMetric (M := M)) where
  flow : SurgeryFlowData.{u}
  schedule : GlobalSurgerySchedule flow.local_constants
  control_function : ℝ → ℝ
  control_antitone : AntitoneOn control_function (Set.Ici 0)
  control_positive : ∀ t ∈ flow.time_domain, 0 < control_function t
  control_eq : ∀ t ∈ flow.time_domain,
    flow.parameters.delta t = control_function t
  schedule_standard_initial : schedule.setup.standard_initial = flow.standard_initial
  parameters_epsilon_eq : flow.parameters.epsilon = schedule.setup.epsilon
  parameters_C_eq : flow.parameters.C = schedule.setup.C
  time_domain_eq : flow.time_domain = Set.Ici 0
  initial_identification : Diffeomorph (𝓡 3) (𝓡 3) M
    (flow.slice 0).carrier ∞
  initial_metric_pullback : ∀ x v w,
    (flow.metric 0).inner (initial_identification x)
      (mfderiv (𝓡 3) (𝓡 3) initial_identification x v)
      (mfderiv (𝓡 3) (𝓡 3) initial_identification x w) =
        N.metric.inner x v w
  no_two_sided_projective_plane : ∀ t ∈ flow.time_domain,
    SurgeryNoTwoSidedProjectivePlane (flow.slice t)
  local_finite : ∀ Kset : Set ℝ, IsCompact Kset →
    (flow.surgery_times ∩ Kset).Finite
  no_finite_accumulation : ∀ T : ℝ, T ∉ flow.surgery_times →
    ∃ d : ℝ, 0 < d ∧
      (flow.surgery_times ∩ Set.Ioo (T - d) (T + d)).Finite
  canonical : SurgeryCanonicalAssumption flow
  noncollapsed : SurgeryNoncollapsed flow
  pinched : SurgeryFlowPinched flow
  admissible : SurgeryFlowAdmissible flow
  schedule_agreement : ∀ j : ℕ, ∀ t ∈ surgeryEpochEntry j,
    t ∈ flow.time_domain →
      flow.parameters.r t = schedule.r j ∧
      flow.parameters.kappa t = schedule.kappa j ∧
      flow.parameters.delta t ≤ schedule.Delta j ∧
      flow.parameters.h t = schedule.setup.selector.h
        (flow.parameters.delta t * flow.parameters.r t)
        (flow.parameters.delta t)
  volume_bound_on_compacts : ∀ Kset : Set ℝ, IsCompact Kset →
    ∃ V : ℝ≥0∞, V ≠ (⊤ : ℝ≥0∞) ∧ ∀ t ∈ flow.time_domain ∩ Kset,
      calibratedMetricVolume (flow.metric t) Set.univ ≤ V




  volume_loss_on_compacts : ∀ Kset : Set ℝ, IsCompact Kset →
    ∃ loss : ∀ (T : ℝ) (_hT : T ∈ flow.surgery_times)
        [Nonempty (flow.slice T).carrier], ℝ≥0∞,
      ∃ sigma : ℝ, 0 < sigma ∧
        ∀ T hT [Nonempty (flow.slice T).carrier], T ∈ Kset →
          (calibratedMetricVolume (flow.metric T) Set.univ + loss T hT ≤
              calibratedMetricVolume (flow.event T hT).limit_metric Set.univ ∧
           ((loss T hT ≠ 0 ∧
            loss T hT ≤ calibratedMetricVolume (flow.event T hT).limit_metric Set.univ) ∨
           (loss T hT = 0 ∧ (flow.event T hT).cap_count = 0)) ∧
           (0 < (flow.event T hT).cap_count →
              ENNReal.ofReal sigma ≤ loss T hT))


  component_event_count_on_compacts : ∀ Kset : Set ℝ, IsCompact Kset →
    ∃ n : ℕ, ∀ S : Finset ℝ,
      (↑S : Set ℝ) ⊆ {T ∈ flow.surgery_times ∩ Kset |
        ∀ (hT : T ∈ flow.surgery_times)
          (hN : Nonempty (flow.slice T).carrier),
          letI := hN
          (flow.event T hT).cap_count = 0} →
      S.card ≤ n
  volume_growth_on_compacts : ∀ Kset : Set ℝ, IsCompact Kset →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℝ,
      a ∈ flow.time_domain ∩ Kset → b ∈ flow.time_domain ∩ Kset → a ≤ b →
      calibratedMetricVolume (flow.metric b) Set.univ ≤
        ENNReal.ofReal (Real.exp (C * (b - a))) *
          calibratedMetricVolume (flow.metric a) Set.univ
  no_surgery_after_empty : ∀ s : ℝ, s ∈ flow.time_domain →
    IsEmpty (flow.slice s).carrier → ∀ t : ℝ, t ∈ flow.time_domain →
      s < t → t ∉ flow.surgery_times
  permanent_empty : ∀ s t : ℝ, s ∈ flow.time_domain → t ∈ flow.time_domain →
    s ≤ t → IsEmpty (flow.slice s).carrier → IsEmpty (flow.slice t).carrier

end PoincareConjecture
