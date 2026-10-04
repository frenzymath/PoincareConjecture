import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Cylinder.TrackedBall
import Mathlib.Topology.Order.Basic

/-!
# Selecting actual counterexamples after the uniform cutoff

Failure of Proposition 16.5 supplies an actual eligible cap for each
prescribed positive cutoff. Its birth delta tends to zero whenever
the cutoffs do. Morgan--Tian, Proposition 16.5, pp. 370 and 373-374;
M44 derivation 93.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M44

/-- An actual failure of the frozen persistence alternative, retaining
the original observation, scale profile and geometric hypotheses.
Source: Proposition 16.5, pp. 373-374; M44 derivation 93. -/
structure CapPersistenceCounterexample {constants : MetricSurgeryConstants}
    (setup : SurgeryControlSetup constants) (start rNext A eta theta cutoff : ℝ) where
  /-- The actual physical flow. -/
  flow : SurgeryFlowData.{u}
  /-- Its actual observation interval and model decoration. -/
  observation : SurgeryObservation flow
  /-- The frozen model comparison. -/
  standard_flow_eq : HEq observation.standard_flow setup.standard_flow
  /-- The entire eligible profile uses the preselected cutoff. -/
  fixed_scales : SurgeryFixedScalesOn setup flow observation start rNext cutoff
  /-- Primitive admissibility. -/
  admissible : SurgeryFlowAdmissible flow
  /-- Actual pinching on the physical flow. -/
  pinched : SurgeryFlowPinched flow
  /-- Actual canonical control on the observation interval. -/
  canonical : SurgeryCanonicalOn flow (surgeryObservationInterval observation) rNext
  /-- The cap birth time. -/
  time : ℝ
  /-- The actual surgery at birth. -/
  is_surgery : time ∈ flow.surgery_times
  /-- The actual nonempty birth slice, used by the event and cap index. -/
  birth_nonempty : Nonempty (flow.slice time).carrier
  /-- Birth lies strictly before the observation endpoint. -/
  observation_time : time ∈ surgeryObservationInterval observation
  /-- Birth is in the controlled overlap. -/
  after_start : start ≤ time
  /-- The birth delta obeys the selected cutoff. -/
  birth_delta_le : flow.parameters.delta time ≤ cutoff
  /-- The actual cap of this event. -/
  cap : Fin (@SurgeryFlowData.event flow time is_surgery birth_nonempty).cap_count
  /-- The exact frozen alternative fails. -/
  failure : ¬ @SurgeryCapPersistenceAlternative flow observation time is_surgery
    birth_nonempty cap A eta theta

/-- Failure of the cutoff-first proposition permits any prescribed
positive schedule of actual counterexamples. Source: Proposition
16.5, pp. 373-374; M44 derivation 93. -/
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

/-- The actual birth deltas tend to zero under a vanishing schedule
of counterexample cutoffs. Source: Proposition 16.5, p. 373;
M44 derivation 93. -/
theorem counterexample_birth_delta_tendsto_zero
    {constants : MetricSurgeryConstants} {setup : SurgeryControlSetup constants}
    {start rNext A eta theta : ℝ} {cutoffs : ℕ → ℝ}
    (X : ∀ n, CapPersistenceCounterexample.{u} setup start rNext A eta theta (cutoffs n))
    (hcutoffs : Tendsto cutoffs atTop (𝓝 0)) :
    Tendsto (fun n => (X n).flow.parameters.delta (X n).time) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => ((X n).flow.parameters.delta_pos (X n).time
    (X n).observation_time.1).le) (fun n => (X n).birth_delta_le) hcutoffs

end PoincareMT.M44
