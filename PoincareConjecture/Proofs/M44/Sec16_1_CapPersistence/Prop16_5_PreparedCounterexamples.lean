import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Prop16_5_Counterexamples
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Prop16_5_MaximalSamples
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Cor16_7_InitialExactCutoff










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

attribute [instance] CapPersistenceCounterexample.birth_nonempty

namespace CapPersistenceCounterexample

variable {constants : MetricSurgeryConstants} {setup : SurgeryControlSetup constants}
  {start rNext A eta theta cutoff : ℝ}



noncomputable def assignedDuration
    (X : CapPersistenceCounterexample.{u} setup start rNext A eta theta cutoff) : ℝ :=
  surgeryCapDuration X.time X.observation.H (X.flow.parameters.h X.time) theta



theorem assignedDuration_pos
    (X : CapPersistenceCounterexample.{u} setup start rNext A eta theta cutoff)
    (htheta : 0 < theta) : 0 < X.assignedDuration :=
  surgeryCapDuration_pos X.observation_time.2
    (X.flow.parameters.h_pos X.time X.observation_time.1) htheta



theorem assignedDuration_le
    (X : CapPersistenceCounterexample.{u} setup start rNext A eta theta cutoff) :
    X.assignedDuration ≤ theta :=
  surgeryCapDuration_le (X.flow.parameters.h_pos X.time X.observation_time.1)



theorem assigned_time_mem
    (X : CapPersistenceCounterexample.{u} setup start rNext A eta theta cutoff)
    {s : ℝ} (hs : s ∈ Ico 0 X.assignedDuration) :
    X.time + s / ((X.flow.parameters.h X.time)⁻¹ ^ 2) ∈
      surgeryObservationInterval X.observation ∩ Ici start := by
  have ht := surgeryCap_physical_time_mem
    (X.flow.parameters.h_pos X.time X.observation_time.1) hs
  exact ⟨⟨X.observation_time.1.trans ht.1, ht.2.trans_le (min_le_left _ _)⟩,
    X.after_start.trans ht.1⟩

end CapPersistenceCounterexample




structure PreparedCapCounterexample {constants : MetricSurgeryConstants}
    (setup : SurgeryControlSetup constants) (start rNext A eta theta cutoff R : ℝ) where

  data : CapPersistenceCounterexample.{u} setup start rNext A eta theta cutoff

  sample : @MaximalCapSample setup.standard_initial data.flow data.time data.is_surgery
    data.birth_nonempty data.cap data.assignedDuration

  radius_eq : sample.radius = R

  comparison_neck : ((@SurgeryFlowData.event data.flow data.time data.is_surgery
    data.birth_nonempty).necks data.cap).neck.epsilon ≤
      data.flow.local_constants.comparison_delta sample.eta




theorem exists_prepared_cap_counterexamples
    (P : M44CapPersistencePredecessors.{u})
    {constants : MetricSurgeryConstants} (setup : SurgeryControlSetup constants)
    (start rNext A eta theta R : ℝ) (htheta : 0 < theta) (hR : 0 < R)
    (hnot : ¬ ∃ cutoff : ℝ, 0 < cutoff ∧
      ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
        HEq O.standard_flow setup.standard_flow →
        SurgeryFixedScalesOn setup F O start rNext cutoff →
        SurgeryFlowAdmissible F → SurgeryFlowPinched F →
        SurgeryCanonicalOn F (surgeryObservationInterval O) rNext →
        ∀ (t : ℝ) (hT : t ∈ F.surgery_times) [Nonempty (F.slice t).carrier],
          t ∈ surgeryObservationInterval O → start ≤ t → F.parameters.delta t ≤ cutoff →
          ∀ i : Fin (F.event t hT).cap_count,
            SurgeryCapPersistenceAlternative F O t hT i A eta theta) :
    ∃ cutoffs : ℕ → ℝ, (∀ n, 0 < cutoffs n) ∧ Tendsto cutoffs atTop (𝓝 0) ∧
      ∃ X : ∀ n, PreparedCapCounterexample.{u} setup start rNext A eta theta (cutoffs n) R,
        Tendsto (fun n => (X n).sample.eta) atTop (𝓝 0) := by
  classical
  let accuracy (n : ℕ) : ℝ := (R + (n : ℝ) + 2)⁻¹
  have haccuracy (n : ℕ) : 0 < accuracy n := by dsimp [accuracy]; positivity
  have hfit (n : ℕ) : R < (accuracy n)⁻¹ := by
    dsimp [accuracy]
    rw [inv_inv]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have haccuracy_le (n : ℕ) : accuracy n ≤ 1 / ((n : ℝ) + 1) := by
    dsimp only [accuracy]
    rw [inv_eq_one_div]
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have haccuracy_lim : Tendsto accuracy atTop (𝓝 0) :=
    squeeze_zero (fun n => (haccuracy n).le) haccuracy_le
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hchoose (n : ℕ) := exists_initial_cap_exact_comparison_cutoff.{u}
    setup.standard_initial constants (haccuracy n)
  choose delta hdelta hcomparison using hchoose
  let cutoffs (n : ℕ) := min (delta n) (1 / ((n : ℝ) + 1))
  have hcutoffs (n : ℕ) : 0 < cutoffs n := lt_min (hdelta n) (by positivity)
  have hcutlim : Tendsto cutoffs atTop (𝓝 0) :=
    squeeze_zero (fun n => (hcutoffs n).le) (fun n => min_le_right (delta n) _)
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨X⟩ := counterexamples_at_positive_cutoffs setup start rNext A eta theta
    hnot cutoffs hcutoffs
  have hprepared (n : ℕ) : ∃ Y :
      PreparedCapCounterexample.{u} setup start rNext A eta theta (cutoffs n) R,
      Y.sample.eta = accuracy n := by
    obtain ⟨Q, hlink, hballs⟩ := hcomparison n (X n).flow
      (X n).fixed_scales.standard_initial_eq (X n).fixed_scales.local_constants_eq
      (X n).time (X n).is_surgery
      ((X n).birth_delta_le.trans (min_le_left _ _)) (X n).cap
    have htime (s : ℝ) (hs : s ∈ Ico 0 (X n).assignedDuration) :
        (X n).time + s / (((X n).flow.parameters.h (X n).time)⁻¹ ^ 2) ∈
          (X n).flow.time_domain :=
      (X n).observation.interval_subset ((X n).assigned_time_mem hs).1
    obtain ⟨D, hDR, hDeta, _hDmap⟩ := exists_maximal_cap_sample P
      (X n).flow (X n).time (X n).is_surgery (X n).cap
      (X n).fixed_scales.standard_initial_eq (X n).pinched
      ((X n).assignedDuration_pos htheta) hR (hfit n) htime Q hballs
    refine ⟨⟨X n, D, hDR, ?_⟩, hDeta⟩
    simpa only [hDeta] using hlink
  choose Y hY using hprepared
  refine ⟨cutoffs, hcutoffs, hcutlim, Y, ?_⟩
  simpa only [hY] using haccuracy_lim




theorem prepared_counterexample_duration_subsequence
    {constants : MetricSurgeryConstants} {setup : SurgeryControlSetup constants}
    {start rNext A eta theta R : ℝ} {cutoffs : ℕ → ℝ}
    (X : ∀ n, PreparedCapCounterexample.{u} setup start rNext A eta theta (cutoffs n) R) :
    ∃ c ∈ Icc (0 : ℝ) theta, ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
      Tendsto (fun n => (X (sigma n)).sample.lifetime) atTop (𝓝 c) := by
  simpa only [Function.comp_def] using
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) theta)).tendsto_subseq
      (x := fun n => (X n).sample.lifetime) (fun n =>
        ⟨(X n).sample.lifetime_pos.le,
          (X n).sample.lifetime_le.trans (X n).data.assignedDuration_le⟩)

end PoincareConjecture.M44
