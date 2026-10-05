import PoincareLib.Geometry.RicciFlow.Surgery.Induction.NoncollapseGeometry

/-!
Adapted from Mapher `PoincareMT/Definitions/Ch16/CanonicalInduction.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- The concrete output of Proposition 17.1, after consuming the uniform
noncollapsing output for the same finite prefix. -/
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

end PoincareMT
