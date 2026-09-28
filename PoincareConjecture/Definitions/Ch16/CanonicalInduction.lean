import PoincareConjecture.Definitions.Ch16.NoncollapseInduction

set_option autoImplicit false

universe u

namespace PoincareConjecture



structure SurgeryCanonicalExtension {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) (Q : SurgeryNoncollapseExtension.{u} p) where
  rNext : ℝ
  deltaNext : ℝ
  r_pos : 0 < rNext
  r_le_last : rNext ≤ p.r ⟨p.i, Nat.lt_succ_self _⟩
  delta_pos : 0 < deltaNext
  delta_le_cutoff : deltaNext ≤ Q.cutoff rNext
  canonical : ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
    SurgeryObservationIsNextEpoch p O →
    SurgeryPrefixControls p F O →
    SurgeryFlowAdmissible F →
    SurgeryFlowPinched F →
    SurgeryFlowTerminalPolicyOn F (surgeryObservationInterval O) →
    SurgeryPostPrefixScales p F O rNext deltaNext →
    (∀ t ∈ surgeryObservationInterval O ∩ Set.Ico (surgeryEpochStart (p.i - 1)) O.H,
      F.parameters.delta t ≤ deltaNext) →
    SurgeryCanonicalOn F (surgeryObservationInterval O) rNext

end PoincareConjecture
