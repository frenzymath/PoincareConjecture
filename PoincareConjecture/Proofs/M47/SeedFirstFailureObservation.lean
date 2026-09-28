import PoincareConjecture.Proofs.M47.PrefixMonotone
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Configuration

set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.Proofs.M47

open M46

theorem seed_firstFailure_observedInputs
    {K : MetricSurgeryConstants} {p : SurgeryParameterPrefix K}
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    {rNext cutoff T : ℝ} (hT : 0 < T) (hTO : T ≤ O.H)
    (hstart : surgeryEpochStart p.i < T)
    (hnext : SurgeryObservationIsNextEpoch p O)
    (old : SurgeryPrefixControls p F O)
    (admissible : SurgeryFlowAdmissible F) (pinched : SurgeryFlowPinched F)
    (policy : SurgeryFlowTerminalPolicyOn F (surgeryObservationInterval O))
    (scales : SurgeryPostPrefixScales p F O rNext cutoff)
    (overlap : ∀ t ∈ surgeryObservationInterval O ∩
      Ico (surgeryEpochStart (p.i - 1)) O.H, F.parameters.delta t ≤ cutoff)
    (past : SurgeryCanonicalOn F (Ico 0 T) rNext) :
    ObservedInputs p rNext cutoff F (O.restrictTo T hT hTO) := by
  refine {
    next_epoch := hnext.restrictObservation hTO hstart
    old := old.restrictObservation hTO
    admissible := admissible
    pinched := pinched
    terminal_policy := policy.restrictObservation hTO
    scales := scales.restrictObservation hTO
    canonical := past
    overlap := ?_ }
  intro t ht
  have hobs : t ∈ surgeryObservationInterval O := ⟨ht.1.1, ht.1.2.trans_le hTO⟩
  exact overlap t ⟨hobs, ht.2.1, hobs.2⟩

end PoincareConjecture.Proofs.M47
