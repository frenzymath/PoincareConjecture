import PoincareConjecture.Definitions.M47CanonicalInduction

set_option autoImplicit false

universe u

namespace PoincareConjecture

theorem SurgeryCanonicalExtension.observedControls
    {K : MetricSurgeryConstants} {p : SurgeryParameterPrefix K}
    {Q : SurgeryNoncollapseExtension.{u} p}
    (R : SurgeryCanonicalExtension p Q)
    (F : SurgeryFlowData.{u}) (O : SurgeryObservation F)
    (hnext : SurgeryObservationIsNextEpoch p O)
    (hprefix : SurgeryPrefixControls p F O)
    (hadmissible : SurgeryFlowAdmissible F)
    (hpinched : SurgeryFlowPinched F)
    (terminal_policy : SurgeryFlowTerminalPolicyOn F (surgeryObservationInterval O))
    (scales : SurgeryPostPrefixScales p F O R.rNext R.deltaNext)
    (overlap : ∀ t ∈ surgeryObservationInterval O ∩
      Set.Ico (surgeryEpochStart (p.i - 1)) O.H,
      F.parameters.delta t ≤ R.deltaNext) :
    SurgeryCanonicalOn F (surgeryObservationInterval O) R.rNext ∧
      SurgeryNoncollapsedOn F (surgeryObservationInterval O) Q.kappaNew := by
  have scales' : SurgeryPostPrefixScales p F O R.rNext (Q.cutoff R.rNext) := {
    r_eq := scales.r_eq
    delta_le := fun t ht =>
      (scales.delta_le t ht).trans R.delta_le_cutoff
    h_eq := scales.h_eq
  }
  have canonical := R.canonical F O hnext hprefix hadmissible hpinched
    terminal_policy scales overlap
  have overlap' : ∀ t ∈ surgeryObservationInterval O ∩ overlapInterval p,
      F.parameters.delta t ≤ Q.cutoff R.rNext := by
    intro t ht
    have hsource : t ∈ surgeryObservationInterval O ∩
        Set.Ico (surgeryEpochStart (p.i - 1)) O.H :=
      ⟨ht.1, ⟨ht.2.1, ht.1.2⟩⟩
    exact (overlap t hsource).trans R.delta_le_cutoff
  have noncollapsed := Q.noncollapsed R.rNext R.r_pos R.r_le_last F O
    hnext hprefix hadmissible hpinched terminal_policy scales' canonical overlap'
  exact ⟨canonical, noncollapsed⟩

theorem SurgeryCanonicalExtension.observedControls_maximal
    {K : MetricSurgeryConstants} {p : SurgeryParameterPrefix K}
    {Q : SurgeryNoncollapseExtension.{u} p}
    (R : SurgeryCanonicalExtension p Q)
    (F : SurgeryFlowData.{u}) (O : SurgeryObservation F)
    (hmax : SurgeryObservationIsMaximalNextEpoch p O)
    (hprefix : SurgeryPrefixControls p F O)
    (hadmissible : SurgeryFlowAdmissible F)
    (hpinched : SurgeryFlowPinched F)
    (terminal_policy : SurgeryFlowTerminalPolicyOn F (surgeryObservationInterval O))
    (scales : SurgeryPostPrefixScales p F O R.rNext R.deltaNext)
    (overlap : ∀ t ∈ surgeryObservationInterval O ∩
      Set.Ico (surgeryEpochStart (p.i - 1)) O.H,
      F.parameters.delta t ≤ R.deltaNext) :
    SurgeryCanonicalOn F F.time_domain R.rNext ∧
      SurgeryNoncollapsedOn F F.time_domain Q.kappaNew := by
  have h := R.observedControls F O hmax.1 hprefix hadmissible hpinched
    terminal_policy scales overlap
  simpa [surgeryObservationInterval, hmax.2] using h

end PoincareConjecture
