import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_TrackedBall
import Mathlib.Topology.Order.Basic










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44




structure CapPersistenceCounterexample {constants : MetricSurgeryConstants}
    (setup : SurgeryControlSetup constants) (start rNext A eta theta cutoff : ℝ) where

  flow : SurgeryFlowData.{u}

  observation : SurgeryObservation flow

  standard_flow_eq : HEq observation.standard_flow setup.standard_flow

  fixed_scales : SurgeryFixedScalesOn setup flow observation start rNext cutoff

  admissible : SurgeryFlowAdmissible flow

  pinched : SurgeryFlowPinched flow

  canonical : SurgeryCanonicalOn flow (surgeryObservationInterval observation) rNext

  time : ℝ

  is_surgery : time ∈ flow.surgery_times

  birth_nonempty : Nonempty (flow.slice time).carrier

  observation_time : time ∈ surgeryObservationInterval observation

  after_start : start ≤ time

  birth_delta_le : flow.parameters.delta time ≤ cutoff

  cap : Fin (@SurgeryFlowData.event flow time is_surgery birth_nonempty).cap_count

  failure : ¬ @SurgeryCapPersistenceAlternative flow observation time is_surgery
    birth_nonempty cap A eta theta




theorem counterexamples_at_positive_cutoffs
    {constants : MetricSurgeryConstants} (setup : SurgeryControlSetup constants)
    (start rNext A eta theta : ℝ)
    (hnot : ¬ ∃ cutoff : ℝ, 0 < cutoff ∧
      ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
        HEq O.standard_flow setup.standard_flow →
        SurgeryFixedScalesOn setup F O start rNext cutoff →
        SurgeryFlowAdmissible F → SurgeryFlowPinched F →
        SurgeryCanonicalOn F (surgeryObservationInterval O) rNext →
        ∀ (t : ℝ) (hT : t ∈ F.surgery_times) [Nonempty (F.slice t).carrier],
          t ∈ surgeryObservationInterval O → start ≤ t → F.parameters.delta t ≤ cutoff →
          ∀ i : Fin (F.event t hT).cap_count,
            SurgeryCapPersistenceAlternative F O t hT i A eta theta)
    (cutoffs : ℕ → ℝ) (hcutoffs : ∀ n, 0 < cutoffs n) :
    Nonempty (∀ n, CapPersistenceCounterexample.{u} setup start rNext A eta theta (cutoffs n)) := by
  classical
  have hbad (cutoff : ℝ) (hcutoff : 0 < cutoff) :
      Nonempty (CapPersistenceCounterexample.{u} setup start rNext A eta theta cutoff) := by
    by_contra hnone
    apply hnot
    refine ⟨cutoff, hcutoff, ?_⟩
    intro F O hmodel hscales hadmissible hpinch hcanonical t hT hn hobs hstart hdelta i
    by_contra hfailure
    exact hnone ⟨⟨F, O, hmodel, hscales, hadmissible, hpinch, hcanonical, t, hT, hn,
      hobs, hstart, hdelta, i, hfailure⟩⟩
  exact ⟨fun n => Classical.choice (hbad (cutoffs n) (hcutoffs n))⟩




theorem counterexample_birth_delta_tendsto_zero
    {constants : MetricSurgeryConstants} {setup : SurgeryControlSetup constants}
    {start rNext A eta theta : ℝ} {cutoffs : ℕ → ℝ}
    (X : ∀ n, CapPersistenceCounterexample.{u} setup start rNext A eta theta (cutoffs n))
    (hcutoffs : Tendsto cutoffs atTop (𝓝 0)) :
    Tendsto (fun n => (X n).flow.parameters.delta (X n).time) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => ((X n).flow.parameters.delta_pos (X n).time
    (X n).observation_time.1).le) (fun n => (X n).birth_delta_le) hcutoffs

end PoincareConjecture.M44
