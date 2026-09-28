import PoincareConjecture.Proofs.M51.StageSequence
import PoincareConjecture.Proofs.M51.EpochIndex











set_option autoImplicit false

open Set
open scoped ENNReal

universe u

namespace PoincareConjecture.M51

open M51Numerical


structure CompletedStageChain
    (S : RepairedControlledSchedulesData.{u})
    (N : RepairedNoncollapseInductionData S)
    (C : RepairedCanonicalInductionData S N)
    (F₀ : SurgeryFlowData.{u}) (k : ℕ) where

  flow : ℕ → SurgeryFlowData.{u}

  initial : SurgeryFlowExtension F₀

  initial_eq : initial.extended = flow 0

  step : ∀ n, SurgeryFlowExtension (flow n)

  step_eq : ∀ n, (step n).extended = flow (n + 1)

  observation : ∀ n, SurgeryObservation (flow n)

  horizon_eq : ∀ n, (observation n).H = surgeryEpochStart (k + n + 2)

  old_controls : ∀ n,
    SurgeryPrefixControls (prefixAt S N C (k + n)) (flow n) (observation n)

  pinched : ∀ n, SurgeryFlowPinched (flow n)

  terminal_policy : ∀ n,
    SurgeryFlowTerminalPolicyOn (flow n) (flow n).time_domain

  maximal_tail : ∀ n, MaximalTail (flow n)

namespace CompletedStageChain

variable {S : RepairedControlledSchedulesData.{u}}
  {N : RepairedNoncollapseInductionData S}
  {C : RepairedCanonicalInductionData S N}
  {F₀ : SurgeryFlowData.{u}} {k : ℕ}


noncomputable def ofStages
    (stage : ∀ n : ℕ, Σ F : SurgeryFlowData.{u}, EpochStage S N C (k + n) F)
    (hzero : (stage 0).1 = F₀)
    (hadj : ∀ n, (stage (n + 1)).1 = (stage n).2.extension.extended)
    (hboundary : ∀ n,
      (stage n).2.observation.H = surgeryEpochStart (k + n + 2)) :
    CompletedStageChain S N C F₀ k where
  flow n := (stage n).2.extension.extended
  initial := hzero ▸ (stage 0).2.extension
  initial_eq := ComposedExtension.castSource_extended hzero (stage 0).2.extension
  step n := hadj n ▸ (stage (n + 1)).2.extension
  step_eq n := ComposedExtension.castSource_extended (hadj n) (stage (n + 1)).2.extension
  observation n := (stage n).2.observation
  horizon_eq := hboundary
  old_controls n := (stage n).2.old_controls
  pinched n := (stage n).2.pinched
  terminal_policy n := (stage n).2.terminal_policy
  maximal_tail n := (stage n).2.maximal_tail

variable (Q : CompletedStageChain S N C F₀ k)


theorem parameters_eq (n : ℕ) : (Q.flow n).parameters = F₀.parameters := by
  induction n with
  | zero =>
    rw [← Q.initial_eq]
    exact Q.initial.parameters_eq
  | succ n ih =>
    rw [← Q.step_eq n]
    exact (Q.step n).parameters_eq.trans ih


theorem standard_initial_eq (n : ℕ) :
    (Q.flow n).standard_initial = F₀.standard_initial := by
  induction n with
  | zero =>
    rw [← Q.initial_eq]
    exact Q.initial.standard_initial_eq
  | succ n ih =>
    rw [← Q.step_eq n]
    exact (Q.step n).standard_initial_eq.trans ih


theorem local_constants_eq (n : ℕ) :
    (Q.flow n).local_constants = F₀.local_constants := by
  induction n with
  | zero =>
    rw [← Q.initial_eq]
    exact Q.initial.local_constants_eq
  | succ n ih =>
    rw [← Q.step_eq n]
    exact (Q.step n).local_constants_eq.trans ih


theorem standard_initial_setup_eq (n : ℕ) :
    (Q.flow n).standard_initial = S.setup.standard_initial := by
  simpa only [prefix_setup] using (Q.old_controls n).standard_initial_eq


theorem local_constants_setup_eq (n : ℕ) :
    (Q.flow n).local_constants = S.constants :=
  (Q.old_controls n).local_constants_eq


theorem epsilon_setup_eq (n : ℕ) : (Q.flow n).parameters.epsilon = S.setup.epsilon := by
  simpa only [prefix_setup] using (Q.old_controls n).epsilon_eq


theorem C_setup_eq (n : ℕ) : (Q.flow n).parameters.C = S.setup.C := by
  simpa only [prefix_setup] using (Q.old_controls n).C_eq


theorem horizon_strictMono : StrictMono (fun n => (Q.observation n).H) := by
  intro n m hnm
  change (Q.observation n).H < (Q.observation m).H
  rw [Q.horizon_eq, Q.horizon_eq]
  apply epochStart_strictMono
  omega


theorem exists_later_horizon (n : ℕ) (B : ℝ) :
    ∃ m, n ≤ m ∧ B < (Q.observation m).H := by
  let m := max n (epochIndex B)
  have hindex : epochIndex B ≤ m := le_max_right _ _
  refine ⟨m, le_max_left _ _, ?_⟩
  rw [Q.horizon_eq]
  exact (lt_epochStart_index B).trans_le (epochStart_strictMono.monotone (by omega))


theorem exists_lt_horizon (B : ℝ) : ∃ n, B < (Q.observation n).H := by
  obtain ⟨n, _, hn⟩ := Q.exists_later_horizon 0 B
  exact ⟨n, hn⟩


theorem mem_time_domain_of_lt_horizon (n : ℕ) {t : ℝ}
    (ht : 0 ≤ t) (hH : t < (Q.observation n).H) : t ∈ (Q.flow n).time_domain :=
  (Q.observation n).interval_subset ⟨ht, hH⟩


theorem exists_later_time (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ∃ m, n ≤ m ∧ t < (Q.observation m).H ∧ t ∈ (Q.flow m).time_domain := by
  obtain ⟨m, hnm, hH⟩ := Q.exists_later_horizon n t
  exact ⟨m, hnm, hH, Q.mem_time_domain_of_lt_horizon m ht hH⟩


theorem exists_later_interval (n : ℕ) (B : ℝ) :
    ∃ m, n ≤ m ∧ Icc 0 B ⊆ (Q.flow m).time_domain := by
  obtain ⟨m, hnm, hH⟩ := Q.exists_later_horizon n B
  refine ⟨m, hnm, ?_⟩
  intro t ht
  exact Q.mem_time_domain_of_lt_horizon m ht.1 (ht.2.trans_lt hH)

end CompletedStageChain


theorem exists_completed_stage_chain_from
    {S : RepairedControlledSchedulesData.{u}}
    {N : RepairedNoncollapseInductionData S}
    {C : RepairedCanonicalInductionData S N}
    (A : M48AnalyticCalibration S) (P : M48Predecessors.{u})
    (d : ℝ) (hd : (M51Numerical.schedule S N C).Delta 0 ≤ d)
    (count : ∀ (B : ℝ) (V₀ : ℝ≥0∞) (hMin : ℝ),
      0 < B → V₀ ≠ (⊤ : ℝ≥0∞) → 0 < hMin →
      ∃ bound : ℕ, ∀ (G : SurgeryFlowData.{u}) (O : SurgeryObservation G),
        G.standard_initial = S.setup.standard_initial →
        G.local_constants = S.constants → O.H ≤ B →
        RepairedObservedVolumeControls G O →
        calibratedMetricVolume (G.metric 0) univ ≤ V₀ →
        (∀ t ∈ G.surgery_times ∩ surgeryObservationInterval O,
          G.parameters.delta t ≤ d ∧ hMin ≤ G.parameters.h t) →
        ∀ A : Finset ℝ,
          (↑A : Set ℝ) ⊆ G.surgery_times ∩ surgeryObservationInterval O →
            A.card ≤ bound)
    (delta : ℝ → ℝ) {F₀ : SurgeryFlowData.{u}} (k : ℕ)
    (X₀ : EpochStage S N C k F₀)
    (hdelta : ∀ t, 0 ≤ t → F₀.parameters.delta t = delta t)
    (hprofiles : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
      F₀.parameters.r t = (M51Numerical.schedule S N C).r j ∧
      F₀.parameters.kappa t = (M51Numerical.schedule S N C).kappa j ∧
      F₀.parameters.h t = S.setup.selector.h
        (delta t * F₀.parameters.r t) (delta t))
    (hcut : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
      delta t ≤ (M51Numerical.schedule S N C).Delta j) :
    Nonempty (CompletedStageChain S N C F₀ k) := by
  obtain ⟨stage, hzero, hstage⟩ :=
    exists_stage_sequence_from A P d hd count delta k X₀ hdelta hprofiles hcut
  exact ⟨CompletedStageChain.ofStages stage hzero
    (fun n => (hstage n).1) (fun n => (hstage n).2.1)⟩

end PoincareConjecture.M51
