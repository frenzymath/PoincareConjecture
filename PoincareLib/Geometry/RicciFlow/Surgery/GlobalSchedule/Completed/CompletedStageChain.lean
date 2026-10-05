import PoincareLib.Geometry.RicciFlow.Surgery.GlobalSchedule.Stage.StageSequence
import PoincareLib.Geometry.RicciFlow.Surgery.GlobalSchedule.Epoch.EpochIndex

/-!
# Completed epoch flows and their adjacent extensions

The first completed flow is an extension of the original source. Each
successor is the target of an explicit extension of the preceding completed
flow. Their observations retain the finite-prefix controls and have dyadic
horizons tending to infinity.
Source: Morgan--Tian Section 17.2, printed pp. 409-411.
-/

set_option autoImplicit false

open Set
open scoped ENNReal

universe u

namespace PoincareMT.M51

open M51Numerical

/-- Completed flows with their actual initial and adjacent extensions and retained controls. -/
structure CompletedStageChain
    (S : RepairedControlledSchedulesData.{u})
    (N : RepairedNoncollapseInductionData S)
    (C : RepairedCanonicalInductionData S N)
    (F₀ : SurgeryFlowData.{u}) (k : ℕ) where
  /-- The actual target of each completed epoch. -/
  flow : ℕ → SurgeryFlowData.{u}
  /-- The retained extension from the original input flow. -/
  initial : SurgeryFlowExtension F₀
  /-- The first completed flow is the initial extension's target. -/
  initial_eq : initial.extended = flow 0
  /-- The actual extension from one completed flow to the next. -/
  step : ∀ n, SurgeryFlowExtension (flow n)
  /-- Each adjacent extension reaches the following completed flow. -/
  step_eq : ∀ n, (step n).extended = flow (n + 1)
  /-- The completed observation on each flow. -/
  observation : ∀ n, SurgeryObservation (flow n)
  /-- Completed observations end at the prescribed dyadic boundaries. -/
  horizon_eq : ∀ n, (observation n).H = surgeryEpochStart (k + n + 2)
  /-- The literal finite-prefix controls retained at completion. -/
  old_controls : ∀ n,
    SurgeryPrefixControls (prefixAt S N C (k + n)) (flow n) (observation n)
  /-- Each finite flow remains pinched on its whole domain. -/
  pinched : ∀ n, SurgeryFlowPinched (flow n)
  /-- Each finite flow retains the actual terminal-event policy. -/
  terminal_policy : ∀ n,
    SurgeryFlowTerminalPolicyOn (flow n) (flow n).time_domain
  /-- The actual maximal ordinary tail retained by each completed stage. -/
  maximal_tail : ∀ n, MaximalTail (flow n)

namespace CompletedStageChain

variable {S : RepairedControlledSchedulesData.{u}}
  {N : RepairedNoncollapseInductionData S}
  {C : RepairedCanonicalInductionData S N}
  {F₀ : SurgeryFlowData.{u}} {k : ℕ}

/-- Extract completed flows and explicit adjacent maps from the dependent stage sequence. -/
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

/-- Every completed flow keeps the input's entire parameter record. -/
theorem parameters_eq (n : ℕ) : (Q.flow n).parameters = F₀.parameters := by
  induction n with
  | zero =>
    rw [← Q.initial_eq]
    exact Q.initial.parameters_eq
  | succ n ih =>
    rw [← Q.step_eq n]
    exact (Q.step n).parameters_eq.trans ih

/-- Every completed flow keeps the input's standard initial model. -/
theorem standard_initial_eq (n : ℕ) :
    (Q.flow n).standard_initial = F₀.standard_initial := by
  induction n with
  | zero =>
    rw [← Q.initial_eq]
    exact Q.initial.standard_initial_eq
  | succ n ih =>
    rw [← Q.step_eq n]
    exact (Q.step n).standard_initial_eq.trans ih

/-- Every completed flow keeps the input's local surgery constants. -/
theorem local_constants_eq (n : ℕ) :
    (Q.flow n).local_constants = F₀.local_constants := by
  induction n with
  | zero =>
    rw [← Q.initial_eq]
    exact Q.initial.local_constants_eq
  | succ n ih =>
    rw [← Q.step_eq n]
    exact (Q.step n).local_constants_eq.trans ih

/-- The retained prefix identifies each completed flow's standard model with the setup. -/
theorem standard_initial_setup_eq (n : ℕ) :
    (Q.flow n).standard_initial = S.setup.standard_initial := by
  simpa only [prefix_setup] using (Q.old_controls n).standard_initial_eq

/-- The retained prefix identifies each completed flow's constants with the setup. -/
theorem local_constants_setup_eq (n : ℕ) :
    (Q.flow n).local_constants = S.constants :=
  (Q.old_controls n).local_constants_eq

/-- Each completed flow uses the setup's prescribed epsilon. -/
theorem epsilon_setup_eq (n : ℕ) : (Q.flow n).parameters.epsilon = S.setup.epsilon := by
  simpa only [prefix_setup] using (Q.old_controls n).epsilon_eq

/-- Each completed flow uses the setup's prescribed cap constant. -/
theorem C_setup_eq (n : ℕ) : (Q.flow n).parameters.C = S.setup.C := by
  simpa only [prefix_setup] using (Q.old_controls n).C_eq

/-- Completed observation horizons are strictly increasing. -/
theorem horizon_strictMono : StrictMono (fun n => (Q.observation n).H) := by
  intro n m hnm
  change (Q.observation n).H < (Q.observation m).H
  rw [Q.horizon_eq, Q.horizon_eq]
  apply epochStart_strictMono
  omega

/-- Beyond any stage there is an observation whose horizon strictly exceeds any given time. -/
theorem exists_later_horizon (n : ℕ) (B : ℝ) :
    ∃ m, n ≤ m ∧ B < (Q.observation m).H := by
  let m := max n (epochIndex B)
  have hindex : epochIndex B ≤ m := le_max_right _ _
  refine ⟨m, le_max_left _ _, ?_⟩
  rw [Q.horizon_eq]
  exact (lt_epochStart_index B).trans_le (epochStart_strictMono.monotone (by omega))

/-- Completed observation horizons are unbounded above. -/
theorem exists_lt_horizon (B : ℝ) : ∃ n, B < (Q.observation n).H := by
  obtain ⟨n, _, hn⟩ := Q.exists_later_horizon 0 B
  exact ⟨n, hn⟩

/-- A nonnegative time strictly before an observation horizon belongs to its raw flow. -/
theorem mem_time_domain_of_lt_horizon (n : ℕ) {t : ℝ}
    (ht : 0 ≤ t) (hH : t < (Q.observation n).H) : t ∈ (Q.flow n).time_domain :=
  (Q.observation n).interval_subset ⟨ht, hH⟩

/-- Every nonnegative time belongs to an observed flow at an arbitrarily late stage. -/
theorem exists_later_time (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ∃ m, n ≤ m ∧ t < (Q.observation m).H ∧ t ∈ (Q.flow m).time_domain := by
  obtain ⟨m, hnm, hH⟩ := Q.exists_later_horizon n t
  exact ⟨m, hnm, hH, Q.mem_time_domain_of_lt_horizon m ht hH⟩

/-- Every bounded nonnegative interval lies in a sufficiently late completed flow. -/
theorem exists_later_interval (n : ℕ) (B : ℝ) :
    ∃ m, n ≤ m ∧ Icc 0 B ⊆ (Q.flow m).time_domain := by
  obtain ⟨m, hnm, hH⟩ := Q.exists_later_horizon n B
  refine ⟨m, hnm, ?_⟩
  intro t ht
  exact Q.mem_time_domain_of_lt_horizon m ht.1 (ht.2.trans_lt hH)

end CompletedStageChain

/-- The finite-completion inputs construct an actual completed chain from any epoch offset. -/
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

end PoincareMT.M51
