import PoincareConjecture.Proofs.M51.GlobalVolumeAssembly
import PoincareConjecture.Definitions.M51GlobalSchedule











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M51

private theorem schedule_on_flow {K : MetricSurgeryConstants}
    (schedule : GlobalSurgerySchedule K) (F : SurgeryFlowData.{u})
    (hK : F.local_constants = K)
    (hepsilon : F.parameters.epsilon = schedule.setup.epsilon)
    (hC : F.parameters.C = schedule.setup.C)
    (hstandard : schedule.setup.standard_initial = F.standard_initial)
    (hagreement : ∀ j t, t ∈ surgeryEpochEntry j → t ∈ F.time_domain →
      F.parameters.r t = schedule.r j ∧
      F.parameters.kappa t = schedule.kappa j ∧
      F.parameters.delta t ≤ schedule.Delta j ∧
      F.parameters.h t = schedule.setup.selector.h
        (F.parameters.delta t * F.parameters.r t) (F.parameters.delta t)) :
    ∃ target : GlobalSurgerySchedule F.local_constants,
      HEq target schedule ∧ F.parameters.epsilon = target.setup.epsilon ∧
      F.parameters.C = target.setup.C ∧
      target.setup.standard_initial = F.standard_initial ∧
      ∀ j t, t ∈ surgeryEpochEntry j → t ∈ F.time_domain →
        F.parameters.r t = target.r j ∧
        F.parameters.kappa t = target.kappa j ∧
        F.parameters.delta t ≤ target.Delta j ∧
        F.parameters.h t = target.setup.selector.h
          (F.parameters.delta t * F.parameters.r t) (F.parameters.delta t) := by
  cases hK
  exact ⟨schedule, HEq.rfl, hepsilon, hC, hstandard, hagreement⟩



theorem normalizedAssembly
    (S : RepairedControlledSchedulesData.{u})
    (N : RepairedNoncollapseInductionData S)
    (C : RepairedCanonicalInductionData S N)
    (H13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (F50 : RepairedFinitePrefixTheory.{u})
    (d : ℝ) (hd : (M51Numerical.schedule S N C).Delta 0 ≤ d)
    (losses : ∀ (F : SurgeryFlowData.{u}) (V : RepairedVolumeLossControls F),
      F.standard_initial = S.standard_initial → F.local_constants = S.constants →
      (∀ t ∈ F.surgery_times, F.parameters.delta t ≤ d) →
      Nonempty (RepairedVolumeLossData F V))
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [T3Space M] [SecondCountableTopology M]
    (I : NormalizedInitialMetric (M := M)) {F₀ : SurgeryFlowData.{u}}
    (R : RepairedGlobalControlledExtension (M51Numerical.schedule S N C) F₀)
    (hstandard₀ : F₀.standard_initial = S.setup.standard_initial)
    (hconstants₀ : F₀.local_constants = S.constants)
    (hepsilon₀ : F₀.parameters.epsilon = S.setup.epsilon)
    (hC₀ : F₀.parameters.C = S.setup.C)
    (e₀ : Diffeomorph (𝓡 3) (𝓡 3) M (F₀.slice 0).carrier ∞)
    (hmetric₀ : ∀ x v w,
      (F₀.metric 0).inner (e₀ x)
        (mfderiv (𝓡 3) (𝓡 3) e₀ x v) (mfderiv (𝓡 3) (𝓡 3) e₀ x w) =
          I.metric.inner x v w)
    (delta : ℝ → ℝ) (hmono : AntitoneOn delta (Ici 0))
    (hpos : ∀ t, 0 ≤ t → 0 < delta t)
    (hdelta : ∀ t, 0 ≤ t → F₀.parameters.delta t = delta t) :
    ∃ G : RepairedGlobalScheduleData I,
      G.flow = R.extension.extended ∧ G.flow.local_constants = S.constants ∧
      HEq G.schedule (M51Numerical.schedule S N C) ∧ G.control_function = delta := by
  let F := R.extension.extended
  have hconstants : F.local_constants = S.constants :=
    R.extension.local_constants_eq.trans hconstants₀
  have hstandard : F.standard_initial = S.setup.standard_initial :=
    R.extension.standard_initial_eq.trans hstandard₀
  have hepsilon : F.parameters.epsilon = S.setup.epsilon :=
    (congrArg (fun p : SurgeryParameters => p.epsilon) R.extension.parameters_eq).trans
      hepsilon₀
  have hC : F.parameters.C = S.setup.C :=
    (congrArg (fun p : SurgeryParameters => p.C) R.extension.parameters_eq).trans hC₀
  obtain ⟨V, ⟨finite⟩⟩ := selected_global_volume S N C H13 F50 d hd losses F
    (hstandard.trans S.setup_standard_initial_eq) hconstants R.admissible R.pinched
    (fun j t hj ht => (R.schedule_agreement j t hj ht).2.2.1)
  obtain ⟨target, htarget, hepsilon', hC', hstandard', hagreement⟩ :=
    schedule_on_flow (M51Numerical.schedule S N C) F hconstants hepsilon hC
      hstandard.symm R.schedule_agreement
  let e₁ := R.extension.identify 0 F₀.zero_mem
  have hmetric : ∀ x v w,
      (F.metric 0).inner ((e₀.trans e₁) x)
        (mfderiv (𝓡 3) (𝓡 3) (e₀.trans e₁) x v)
        (mfderiv (𝓡 3) (𝓡 3) (e₀.trans e₁) x w) = I.metric.inner x v w := by
    intro x v w
    change (F.metric 0).inner (e₁ (e₀ x))
      (mfderiv (𝓡 3) (𝓡 3) (e₁ ∘ e₀) x v)
      (mfderiv (𝓡 3) (𝓡 3) (e₁ ∘ e₀) x w) = _
    rw [mfderiv_comp x (e₁.contMDiff.mdifferentiable (by simp) (e₀ x))
      (e₀.contMDiff.mdifferentiable (by simp) x)]
    change (F.metric 0).inner (e₁ (e₀ x))
      (mfderiv (𝓡 3) (𝓡 3) e₁ (e₀ x) (mfderiv (𝓡 3) (𝓡 3) e₀ x v))
      (mfderiv (𝓡 3) (𝓡 3) e₁ (e₀ x) (mfderiv (𝓡 3) (𝓡 3) e₀ x w)) = _
    rw [R.extension.metric_pullback]
    exact hmetric₀ x v w
  let G : RepairedGlobalScheduleData I := {
    flow := F
    schedule := target
    prefix_witness := globalSurgeryPrefixWitness_of_schedule target
    control_function := delta
    control_antitone := hmono
    control_positive := fun t ht => hpos t (F.time_domain_nonnegative ht)
    control_eq := fun t ht =>
      (congrArg (fun p : SurgeryParameters => p.delta t) R.extension.parameters_eq).trans
        (hdelta t (F.time_domain_nonnegative ht))
    parameters_epsilon_eq := hepsilon'
    parameters_C_eq := hC'
    admissible := R.admissible
    terminal_policy := R.terminal_policy
    pinched := R.pinched
    canonical := R.canonical
    noncollapsed := R.noncollapsed
    schedule_standard_initial := hstandard'
    volume_nonempty_pre_interval := F.nonemptyEventPreInterval
    volume_vanishing_pre_interval := F.vanishingEventPreInterval
    volume_zero_cap_discard := F.zeroCapDiscard H13
    volume_loss := V
    time_domain_eq := R.time_domain_eq
    initial_identification := e₀.trans e₁
    initial_metric_pullback := hmetric
    schedule_agreement := hagreement
    local_finite := finite.local_finite }
  exact ⟨G, rfl, hconstants, htarget, rfl⟩

end PoincareConjecture.M51
