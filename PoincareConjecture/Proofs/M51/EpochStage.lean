import PoincareConjecture.Proofs.M51.FirstEpoch
import PoincareConjecture.Proofs.M51.FrontierObservation
import PoincareConjecture.Proofs.M51.ExtensionComposition
import PoincareConjecture.Proofs.M48.NextFrontier
import PoincareConjecture.Proofs.M48.ExtensionControls
import PoincareConjecture.Proofs.M33.ContinuationPolicy

set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.M51

open M51Numerical

structure EpochStage (S : RepairedControlledSchedulesData.{u})
    (N : RepairedNoncollapseInductionData S) (C : RepairedCanonicalInductionData S N)
    (n : ℕ) (F : SurgeryFlowData.{u}) where
  extension : SurgeryFlowExtension F
  observation : SurgeryObservation extension.extended
  old_controls : SurgeryPrefixControls (prefixAt S N C n) extension.extended observation
  pinched : SurgeryFlowPinched extension.extended
  terminal_policy : SurgeryFlowTerminalPolicyOn extension.extended extension.extended.time_domain
  maximal_tail : MaximalTail extension.extended
  start_le : surgeryEpochStart (prefixAt S N C n).i ≤ observation.H
  horizon_le : observation.H ≤ surgeryEpochStart ((prefixAt S N C n).i + 1)
  early_frontier : observation.H < surgeryEpochStart ((prefixAt S N C n).i + 1) →
    extension.extended.time_domain = Ico 0 observation.H

namespace EpochStage

variable {S : RepairedControlledSchedulesData.{u}}
  {N : RepairedNoncollapseInductionData S} {C : RepairedCanonicalInductionData S N}
  {n : ℕ} {F : SurgeryFlowData.{u}}

noncomputable def ofObservation (O : SurgeryObservation F)
    (old : SurgeryPrefixControls (prefixAt S N C n) F O)
    (pinched : SurgeryFlowPinched F)
    (policy : SurgeryFlowTerminalPolicyOn F F.time_domain) (tail : MaximalTail F)
    (hstart : surgeryEpochStart (prefixAt S N C n).i ≤ O.H)
    (hend : O.H ≤ surgeryEpochStart ((prefixAt S N C n).i + 1))
    (hfront : O.H < surgeryEpochStart ((prefixAt S N C n).i + 1) →
      F.time_domain = Ico 0 O.H) : EpochStage S N C n F where
  extension := SurgeryFlowExtension.refl F
  observation := O
  old_controls := old
  pinched := pinched
  terminal_policy := policy
  maximal_tail := tail
  start_le := hstart
  horizon_le := hend
  early_frontier := hfront

variable (X : EpochStage S N C n F) {delta : ℝ → ℝ}

noncomputable def rebase : EpochStage S N C n X.extension.extended :=
  ofObservation X.observation X.old_controls X.pinched X.terminal_policy X.maximal_tail
    X.start_le X.horizon_le X.early_frontier

theorem delta_eq
    (hdelta : ∀ t, 0 ≤ t → F.parameters.delta t = delta t) :
    ∀ t, 0 ≤ t → X.extension.extended.parameters.delta t = delta t := by
  simpa only [X.extension.parameters_eq] using hdelta

theorem profiles
    (hprofiles : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
      F.parameters.r t = (schedule S N C).r j ∧
      F.parameters.kappa t = (schedule S N C).kappa j ∧
      F.parameters.h t = S.setup.selector.h (delta t * F.parameters.r t) (delta t)) :
    ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
      X.extension.extended.parameters.r t = (schedule S N C).r j ∧
      X.extension.extended.parameters.kappa t = (schedule S N C).kappa j ∧
      X.extension.extended.parameters.h t = S.setup.selector.h
        (delta t * X.extension.extended.parameters.r t) (delta t) := by
  simpa only [X.extension.parameters_eq] using hprofiles

theorem controls
    (hdelta : ∀ t, 0 ≤ t → F.parameters.delta t = delta t)
    (hprofiles : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
      F.parameters.r t = (schedule S N C).r j ∧
      F.parameters.kappa t = (schedule S N C).kappa j ∧
      F.parameters.h t = S.setup.selector.h (delta t * F.parameters.r t) (delta t))
    (hcut : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
      delta t ≤ (schedule S N C).Delta j) :
    SurgeryEpochContinuationControls (prefixAt S N C n)
      X.extension.extended X.observation (noncollapse S N C n) (canonical S N C n) ∧
    SurgeryNoncollapsedOn X.extension.extended (surgeryObservationInterval X.observation)
      (noncollapse S N C n).kappaNew :=
  have terminal_policy : SurgeryFlowTerminalPolicyOn X.extension.extended
      (surgeryObservationInterval X.observation) :=
    X.terminal_policy.restrict (by
      simpa only [surgeryObservationInterval] using X.observation.interval_subset)
  continuationControls S N C n _ _ delta (X.delta_eq hdelta) (X.profiles hprofiles)
    hcut X.old_controls X.pinched terminal_policy X.start_le X.horizon_le

theorem advance (A : M48AnalyticCalibration S) (P : M48Predecessors.{u})
    (hdelta : ∀ t, 0 ≤ t → F.parameters.delta t = delta t)
    (hprofiles : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
      F.parameters.r t = (schedule S N C).r j ∧
      F.parameters.kappa t = (schedule S N C).kappa j ∧
      F.parameters.h t = S.setup.selector.h (delta t * F.parameters.r t) (delta t))
    (hcut : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
      delta t ≤ (schedule S N C).Delta j)
    (hlt : X.observation.H < surgeryEpochStart ((prefixAt S N C n).i + 1)) :
    ∃ Y : EpochStage S N C n F,
      X.observation.H < Y.observation.H ∧
      X.observation.H ∈ Y.extension.extended.surgery_times ∧
      X.extension.extended.surgery_times ⊆ Y.extension.extended.surgery_times := by
  obtain ⟨L⟩ := X.maximal_tail.slab_of_domain_eq X.observation.H_pos (X.early_frontier hlt)
  obtain ⟨guards, _⟩ := X.controls hdelta hprofiles hcut
  obtain ⟨_geom, _reference, _H, _limit, _horn, _href, _hr, _he, _hC, _hA,
      _htimes, _hlimit, _bridge, branch, O', hprogress, hbound, hsurgery,
      _hfree, hfrontier, _hslab, _hstandard⟩ :=
    A.singular_frontier P (compatible S N C n) X.old_controls guards
      X.start_le hlt (X.early_frontier hlt) L
  have target_policy : SurgeryFlowTerminalPolicyOn
      branch.conclusion.extension.extended (surgeryObservationInterval O') := by
    apply SurgeryFlowTerminalPolicyOn.restrict (F := branch.conclusion.extension.extended)
      (J := surgeryObservationInterval O')
      (K := branch.conclusion.extension.extended.time_domain)
    · simpa only [surgeryObservationInterval] using O'.interval_subset
    · exact branch.conclusion.terminalPolicy X.terminal_policy
  obtain ⟨old', _hcanonical, _hnoncollapsed⟩ :=
    branch.observedControls X.old_controls guards O' X.start_le
      ⟨X.start_le.trans_lt hprogress, hbound⟩ target_policy P.m13
  let Y : EpochStage S N C n F := {
    extension := X.extension.trans branch.conclusion.extension
    observation := O'
    old_controls := old'
    pinched := branch.conclusion.pinched
    terminal_policy := branch.conclusion.terminalPolicy X.terminal_policy
    maximal_tail := maximalTail_of_restart branch.conclusion
    start_le := X.start_le.trans hprogress.le
    horizon_le := hbound
    early_frontier := fun h => (hfrontier h).1 }
  refine ⟨Y, hprogress, hsurgery, ?_⟩
  intro t ht
  exact (branch.conclusion.extension.old_surgery_times t
    (X.extension.extended.surgery_times_subset ht)).2 ht

theorem promote
    (hdelta : ∀ t, 0 ≤ t → F.parameters.delta t = delta t)
    (hprofiles : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
      F.parameters.r t = (schedule S N C).r j ∧
      F.parameters.kappa t = (schedule S N C).kappa j ∧
      F.parameters.h t = S.setup.selector.h (delta t * F.parameters.r t) (delta t))
    (hcut : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
      delta t ≤ (schedule S N C).Delta j)
    (hboundary : X.observation.H = surgeryEpochStart ((prefixAt S N C n).i + 1)) :
    ∃ Y : EpochStage S N C (n + 1) F,
      Y.extension = X.extension ∧ X.observation.H ≤ Y.observation.H := by
  obtain ⟨guards, hnoncollapsed⟩ := X.controls hdelta hprofiles hcut
  have old' : SurgeryPrefixControls (prefixAt S N C (n + 1))
      X.extension.extended X.observation :=
    X.old_controls.nextPrefix guards.canonical hnoncollapsed guards.next_r
      guards.next_kappa guards.next_h guards.overlap_delta
  have hstart : surgeryEpochStart (prefixAt S N C (n + 1)).i = X.observation.H := by
    rw [hboundary, prefix_index, prefix_index]
  have hbound : X.observation.H ≤ surgeryEpochStart ((prefixAt S N C (n + 1)).i + 1) := by
    rw [← hstart]
    exact epochStart_strictMono.monotone (Nat.le_succ _)
  obtain ⟨O', hprogress, hend, _hstandard, hfront, _hslab⟩ :=
    X.maximal_tail.observeBefore X.observation hbound
  refine ⟨{
    extension := X.extension
    observation := O'
    old_controls := old'.observePastPrefix O' hstart.le X.pinched
    pinched := X.pinched
    terminal_policy := X.terminal_policy
    maximal_tail := X.maximal_tail
    start_le := hstart.le.trans hprogress
    horizon_le := hend
    early_frontier := hfront }, rfl, hprogress⟩

end EpochStage
end PoincareConjecture.M51
