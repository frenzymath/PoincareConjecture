import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Extension.ExtensionPrefix
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Extension.CanonicalControls
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochData

/-!
# Selected controls on the actual restarted flow

Morgan--Tian Section 17.2, pp. 409-410. Transport the already prescribed
parameter profiles, then apply Proposition 17.1 followed by Proposition
16.1 on the literal M33 branch and its observation. No analytic configuration
or control on the newly added times is an input of this adapter.
-/

set_option autoImplicit false

open Set

universe u

namespace PoincareMT

private theorem epochStart_mono : Monotone surgeryEpochStart := by
  intro i j hij
  exact div_le_div_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hij) (by norm_num)

/-- The selected canonical and noncollapse services control the same actual
restart, including an observation at the next epoch boundary or in an empty
continuation. Earlier-prefix controls are transported through its own maps. -/
theorem RepairedBranchContinuationData.observedControls
    {K : MetricSurgeryConstants} {p : SurgeryParameterPrefix K}
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F} {T : ℝ}
    {I : RepairedContinuationInput F T} (branch : RepairedBranchContinuationData I)
    {Q : SurgeryNoncollapseExtension.{u} p} {R : SurgeryCanonicalExtension p Q}
    (old : SurgeryPrefixControls p F O)
    (controls : SurgeryEpochContinuationControls p F O Q R)
    (O' : SurgeryObservation branch.conclusion.extension.extended)
    (hstart : surgeryEpochStart p.i ≤ O.H)
    (hnext : SurgeryObservationIsNextEpoch p O')
    (terminal_policy : SurgeryFlowTerminalPolicyOn
      branch.conclusion.extension.extended (surgeryObservationInterval O'))
    (m13 : GeneralizedParabolicRescalingTheory.{u} 3) :
    SurgeryPrefixControls p branch.conclusion.extension.extended O' ∧
      SurgeryCanonicalOn branch.conclusion.extension.extended
        (surgeryObservationInterval O') R.rNext ∧
      SurgeryNoncollapsedOn branch.conclusion.extension.extended
        (surgeryObservationInterval O') Q.kappaNew := by
  have hprefix := branch.prefixControls old O' hstart m13
  have hepoch {t : ℝ}
      (ht : t ∈ surgeryObservationInterval O' ∩ Ici (surgeryEpochStart p.i)) :
      t ∈ surgeryEpoch p.i :=
    ⟨ht.2, ht.1.2.trans_le hnext.2⟩
  have hoverlap {t : ℝ} (ht : t ∈ surgeryEpoch p.i) :
      t ∈ overlapInterval p :=
    ⟨(epochStart_mono (Nat.sub_le p.i 1)).trans ht.1, ht.2⟩
  have scales : SurgeryPostPrefixScales p branch.conclusion.extension.extended
      O' R.rNext R.deltaNext := {
    r_eq := by
      intro t ht
      simpa only [branch.conclusion.extension.parameters_eq] using
        controls.next_r t (hepoch ht)
    delta_le := by
      intro t ht
      simpa only [branch.conclusion.extension.parameters_eq] using
        controls.overlap_delta t (hoverlap (hepoch ht))
    h_eq := by
      intro t ht
      simpa only [branch.conclusion.extension.parameters_eq] using
        controls.next_h t (hepoch ht)
  }
  have overlap : ∀ t ∈ surgeryObservationInterval O' ∩
      Ico (surgeryEpochStart (p.i - 1)) O'.H,
      branch.conclusion.extension.extended.parameters.delta t ≤ R.deltaNext := by
    intro t ht
    have ht' : t ∈ overlapInterval p := ⟨ht.2.1, ht.1.2.trans_le hnext.2⟩
    simpa only [branch.conclusion.extension.parameters_eq] using
      controls.overlap_delta t ht'
  exact ⟨hprefix, R.observedControls _ O' hnext hprefix
    branch.conclusion.admissible branch.conclusion.pinched terminal_policy scales overlap⟩

end PoincareMT
