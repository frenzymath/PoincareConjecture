import PoincareConjecture.Proofs.M47.SeedFirstFailureObservation
import PoincareConjecture.Proofs.M47.NoncollapseHorizon
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_ObservedWindow









set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.Proofs.M47



theorem seed_firstFailure_noncollapsed
    (P : M47Predecessors.{u}) {K : MetricSurgeryConstants}
    {p : SurgeryParameterPrefix K} (Q : SurgeryNoncollapseExtension.{u} p)
    {rNext cutoff : ℝ} (hr : 0 < rNext) (hrLast : rNext ≤ p.r (Fin.last p.i))
    (hcutoff : cutoff ≤ Q.cutoff rNext)
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (hnext : SurgeryObservationIsNextEpoch p O)
    (old : SurgeryPrefixControls p F O)
    (admissible : SurgeryFlowAdmissible F) (pinched : SurgeryFlowPinched F)
    (policy : SurgeryFlowTerminalPolicyOn F (surgeryObservationInterval O))
    (scales : SurgeryPostPrefixScales p F O rNext cutoff)
    (overlap : ∀ t ∈ surgeryObservationInterval O ∩
      Ico (surgeryEpochStart (p.i - 1)) O.H, F.parameters.delta t ≤ cutoff)
    {T : ℝ} (ht : T ∈ Ico (surgeryEpochStart p.i) O.H)
    (past : SurgeryCanonicalOn F (Ico 0 T) rNext) :
    SurgeryNoncollapsedOn F (Icc 0 T) Q.kappaNew := by
  have hstart : 0 < surgeryEpochStart p.i := by
    unfold surgeryEpochStart
    positivity
  have hT : 0 < T := hstart.trans_le ht.1
  apply surgeryNoncollapsedOn_closed_horizon P hT
  rcases lt_or_eq_of_le ht.1 with hstrict | heq
  · have inputs := (seed_firstFailure_observedInputs hT ht.2.le hstrict hnext
      old admissible pinched policy scales overlap past).cutoff_mono hcutoff
    exact Q.noncollapsed rNext hr hrLast F (O.restrictTo T hT ht.2.le)
      inputs.next_epoch inputs.old inputs.admissible inputs.pinched
      inputs.terminal_policy inputs.scales inputs.canonical inputs.overlap
  · rw [← heq]
    exact old.noncollapsedOn_before_prefixEnd hnext.1.le Q.kappa_le_last

end PoincareConjecture.Proofs.M47
