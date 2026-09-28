import PoincareConjecture.Proofs.M48.ExtensionNoncollapse
import PoincareConjecture.Definitions.M33BranchContinuation











set_option autoImplicit false

universe u

namespace PoincareConjecture

private theorem epochStart_mono : Monotone surgeryEpochStart := by
  intro i j hij
  exact div_le_div_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hij) (by norm_num)

private theorem oldEntry_before_horizon {K : MetricSurgeryConstants}
    {p : SurgeryParameterPrefix K} {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (hstart : surgeryEpochStart p.i ≤ O.H) {j : ℕ} (hj : j ≤ p.i)
    {t : ℝ} (ht : t ∈ surgeryEpochEntry j) (ht0 : 0 ≤ t) :
    t ∈ surgeryObservationInterval O := by
  have htj : t < surgeryEpochStart j := by
    unfold surgeryEpochEntry at ht
    split at ht
    · rename_i hj
      simpa only [hj] using ht.2
    · exact ht.2
  exact ⟨ht0, (htj.trans_le (epochStart_mono hj)).trans_le hstart⟩


theorem SurgeryPrefixControls.onExtension
    {K : MetricSurgeryConstants} {p : SurgeryParameterPrefix K}
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (old : SurgeryPrefixControls p F O) (E : SurgeryFlowExtension F)
    (O' : SurgeryObservation E.extended)
    (hstart : surgeryEpochStart p.i ≤ O.H)
    (m13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (hadmissible : SurgeryFlowAdmissible E.extended)
    (hpinched : SurgeryFlowPinched E.extended) : SurgeryPrefixControls p E.extended O' := by
  have hold (j : Fin (p.i + 1)) (hj : j.val ≤ p.i) {t : ℝ}
      (ht : t ∈ surgeryObservationInterval O' ∩ surgeryEpochEntry j.val) :
      t ∈ surgeryObservationInterval O ∩ surgeryEpochEntry j.val :=
    ⟨oldEntry_before_horizon hstart hj ht.2 ht.1.1, ht.2⟩
  refine {
    standard_initial_eq := E.standard_initial_eq.trans old.standard_initial_eq
    local_constants_eq := E.local_constants_eq.trans old.local_constants_eq
    epsilon_eq := ?_
    C_eq := ?_
    admissible := hadmissible
    pinched := fun t _ ht => hpinched t ht
    canonical := ?_
    noncollapsed := ?_
    delta_bound := ?_
    r_schedule := ?_
    kappa_schedule := ?_
    h_schedule := ?_
  }
  · simpa only [E.parameters_eq] using old.epsilon_eq
  · simpa only [E.parameters_eq] using old.C_eq
  · intro j hj
    exact E.canonical_on m13 (fun _ ht => O.interval_subset (hold j hj ht).1)
      (fun t ht htF => old.canonical j hj t (hold j hj ht) htF)
  · intro j hj
    exact E.noncollapsed_on m13 (fun _ ht => O.interval_subset (hold j hj ht).1)
      (fun t ht htF => old.noncollapsed j hj t (hold j hj ht) htF)
  · intro j hj t ht
    simpa only [E.parameters_eq] using old.delta_bound j hj t (hold j hj ht)
  · intro j hj t ht
    simpa only [E.parameters_eq] using old.r_schedule j hj t (hold j hj ht)
  · intro j hj t ht
    simpa only [E.parameters_eq] using old.kappa_schedule j hj t (hold j hj ht)
  · intro j hj t ht
    simpa only [E.parameters_eq] using old.h_schedule j hj t (hold j hj ht)


theorem RepairedBranchContinuationData.prefixControls
    {K : MetricSurgeryConstants} {p : SurgeryParameterPrefix K}
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F} {T : ℝ}
    {I : RepairedContinuationInput F T} (branch : RepairedBranchContinuationData I)
    (old : SurgeryPrefixControls p F O)
    (O' : SurgeryObservation branch.conclusion.extension.extended)
    (hstart : surgeryEpochStart p.i ≤ O.H)
    (m13 : GeneralizedParabolicRescalingTheory.{u} 3) :
    SurgeryPrefixControls p branch.conclusion.extension.extended O' :=
  old.onExtension branch.conclusion.extension O' hstart m13
    branch.conclusion.admissible branch.conclusion.pinched

end PoincareConjecture
