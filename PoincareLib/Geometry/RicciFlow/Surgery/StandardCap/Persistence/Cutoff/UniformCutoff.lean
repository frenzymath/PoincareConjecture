import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Cutoff.FiniteContinuation
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Cutoff.SequenceContradiction

/-!
# A uniform cutoff before the flow and observation

Failure of the frozen cutoff-first statement gives actual prepared
counterexamples. Finite continuation of their duration subsequence
contradicts the maximal-cylinder alternative. Morgan--Tian,
Proposition 16.5, pp. 370-375; M44 derivation 113.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

universe u

namespace PoincareMT.M44

/-- The fixed setup and requested comparison choose a positive
cutoff before every eligible flow, observation, event and cap.
Source: Proposition 16.5, pp. 370-375; M44 derivation 113. -/
theorem exists_cap_persistence_cutoff
    (P : M44CapPersistencePredecessors.{u})
    {constants : MetricSurgeryConstants} (setup : SurgeryControlSetup constants)
    (standard : RepairedStandardCapExistenceData setup.standard_initial)
    (unique : RepairedStandardCapUniquenessData setup.standard_initial standard)
    (start rNext A eta theta : ℝ) (hr : 0 < rNext)
    (hA : 0 < A) (heta : 0 < eta) (htheta : 0 < theta) (htheta1 : theta < 1) :
    ∃ cutoff : ℝ, 0 < cutoff ∧
      ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
        HEq O.standard_flow setup.standard_flow →
        SurgeryFixedScalesOn setup F O start rNext cutoff →
        SurgeryFlowAdmissible F → SurgeryFlowPinched F →
        SurgeryCanonicalOn F (surgeryObservationInterval O) rNext →
        ∀ (t : ℝ) (hT : t ∈ F.surgery_times) [Nonempty (F.slice t).carrier],
          t ∈ surgeryObservationInterval O → start ≤ t → F.parameters.delta t ≤ cutoff →
          ∀ i : Fin (F.event t hT).cap_count,
            SurgeryCapPersistenceAlternative F O t hT i A eta theta := by
  by_contra hnot
  have hinner : 0 < A + 1 := by linarith
  obtain ⟨cutoffs, _hpositive, hcutoffs, X, hetaX⟩ :=
    exists_prepared_cap_counterexamples P setup start rNext A eta theta (A + 1)
      htheta hinner hnot
  obtain ⟨c, hc, sigma, hsigma, hlim⟩ := prepared_counterexample_duration_subsequence X
  let Y := fun n => X (sigma n)
  have hcutY : Tendsto (fun n => cutoffs (sigma n)) atTop (𝓝 0) :=
    hcutoffs.comp hsigma.tendsto_atTop
  have hetaY : Tendsto (fun n => (Y n).sample.eta) atTop (𝓝 0) :=
    hetaX.comp hsigma.tendsto_atTop
  obtain ⟨R0, K, hinnerR0, hK, T, hT, hcT, hstage⟩ :=
    exists_cap_sequence_full_stage P setup standard unique hr hinner htheta htheta1
      Y hcutY hetaY hc.1 hc.2 hlim
  exact prepared_counterexamples_contradiction P setup standard unique hA heta htheta htheta1
    Y hcutY hetaY hc.1 hc.2 hlim hinnerR0 hT hcT hK hstage

end PoincareMT.M44
