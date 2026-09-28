import PoincareConjecture.Definitions.M48ParameterExtension
import PoincareConjecture.Definitions.M48EpochExtension
import PoincareConjecture.Proofs.M48.DerivativeControls

set_option autoImplicit false

universe u

namespace PoincareConjecture

theorem RepairedControlledSchedulesData.SeedCompatible.nextPrefix
    {S : RepairedControlledSchedulesData.{u}}
    {p : SurgeryParameterPrefix S.constants} (hp : S.SeedCompatible p)
    (Q : SurgeryNoncollapseExtension.{u} p) (R : SurgeryCanonicalExtension p Q) :
    S.SeedCompatible (p.nextPrefix Q R) := by
  exact {
    setup_eq := (SurgeryParameterPrefix.nextPrefix_setup p Q R).trans hp.setup_eq
    kappa_zero_eq := (SurgeryParameterPrefix.nextPrefix_kappa_zero p Q R).trans
      hp.kappa_zero_eq
    Delta_zero_eq := (SurgeryParameterPrefix.nextPrefix_Delta_zero p Q R).trans
      hp.Delta_zero_eq
  }

private theorem epochStart_mono : Monotone surgeryEpochStart := by
  intro i j hij
  exact div_le_div_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hij) (by norm_num)

private theorem lastEntry_subset_overlap {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) : surgeryEpochEntry p.i ⊆ overlapInterval p := by
  intro t ht
  have hi : p.i ≠ 0 := Nat.ne_of_gt p.i_pos
  simp only [surgeryEpochEntry, hi, if_false, Set.mem_Ico] at ht
  exact ⟨ht.1, ht.2.trans_le (epochStart_mono (Nat.le_succ _))⟩

private theorem nextEpoch_subset_overlap {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) : surgeryEpoch p.i ⊆ overlapInterval p := by
  intro t ht
  exact ⟨(epochStart_mono (Nat.sub_le p.i 1)).trans ht.1, ht.2⟩

private theorem epochEntry_exists
    (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t)
    (htn : t < surgeryEpochStart n) :
    ∃ j : Fin (n + 1), t ∈ surgeryEpochEntry j.val := by
  induction n with
  | zero =>
      refine ⟨0, ?_⟩
      simpa [surgeryEpochEntry] using And.intro ht0 htn
  | succ n ih =>
      by_cases hprev : t < surgeryEpochStart n
      · obtain ⟨j, hj⟩ := ih hprev
        exact ⟨j.castSucc, hj⟩
      · refine ⟨Fin.last (n + 1), ?_⟩
        have hprev' : surgeryEpochStart n ≤ t := le_of_not_gt hprev
        simpa [surgeryEpochEntry, Nat.succ_ne_zero] using And.intro hprev' htn

theorem SurgeryPrefixControls.nextPrefix
    {K : MetricSurgeryConstants} {p : SurgeryParameterPrefix K}
    {Q : SurgeryNoncollapseExtension.{u} p} {R : SurgeryCanonicalExtension p Q}
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (old : SurgeryPrefixControls p F O)
    (canonical : SurgeryCanonicalOn F (surgeryObservationInterval O) R.rNext)
    (noncollapsed : SurgeryNoncollapsedOn F (surgeryObservationInterval O) Q.kappaNew)
    (next_r : ∀ t ∈ surgeryEpoch p.i, F.parameters.r t = R.rNext)
    (next_kappa : ∀ t ∈ surgeryEpoch p.i,
      F.parameters.kappa t = Q.kappaNew)
    (next_h : ∀ t ∈ surgeryEpoch p.i,
      F.parameters.h t = p.setup.selector.h
        (F.parameters.delta t * F.parameters.r t) (F.parameters.delta t))
    (overlap_delta : ∀ t ∈ overlapInterval p, F.parameters.delta t ≤ R.deltaNext) :
    SurgeryPrefixControls (p.nextPrefix Q R) F O := by
  refine {
    standard_initial_eq := old.standard_initial_eq
    local_constants_eq := old.local_constants_eq
    epsilon_eq := old.epsilon_eq
    C_eq := old.C_eq
    admissible := old.admissible
    pinched := old.pinched
    canonical := ?_
    noncollapsed := ?_
    delta_bound := ?_
    r_schedule := ?_
    kappa_schedule := ?_
    h_schedule := ?_
  }
  · change ∀ j : Fin ((p.i + 1) + 1), j.val ≤ p.i + 1 →
      SurgeryCanonicalOn F (surgeryObservationInterval O ∩ surgeryEpochEntry j.val)
        ((p.nextPrefix Q R).r j)
    intro j _hj
    cases j using Fin.lastCases with
    | last =>
        simp only [SurgeryParameterPrefix.nextPrefix_r_last]
        intro t ht htF x hx
        exact canonical t ht.1 htF x hx
    | cast j =>
        simpa only [Fin.val_castSucc, SurgeryParameterPrefix.nextPrefix_r_castSucc]
          using old.canonical j (Nat.le_of_lt_succ j.isLt)
  · change ∀ j : Fin ((p.i + 1) + 1), j.val ≤ p.i + 1 →
      SurgeryNoncollapsedOn F (surgeryObservationInterval O ∩ surgeryEpochEntry j.val)
        ((p.nextPrefix Q R).kappa j)
    intro j _hj
    cases j using Fin.lastCases with
    | last =>
        simp only [SurgeryParameterPrefix.nextPrefix_kappa_last]
        intro t ht htF
        exact noncollapsed t ht.1 htF
    | cast j =>
        simpa only [Fin.val_castSucc, SurgeryParameterPrefix.nextPrefix_kappa_castSucc]
          using old.noncollapsed j (Nat.le_of_lt_succ j.isLt)
  · change ∀ j : Fin ((p.i + 1) + 1), j.val ≤ p.i + 1 →
      ∀ t ∈ surgeryObservationInterval O ∩ surgeryEpochEntry j.val,
        F.parameters.delta t ≤ (p.nextPrefix Q R).Delta j
    intro j _hj
    cases j using Fin.lastCases with
    | last =>
        intro t ht
        have htEpoch : t ∈ surgeryEpoch p.i := by
          simpa [surgeryEpochEntry, surgeryEpoch] using ht.2
        simpa only [SurgeryParameterPrefix.nextPrefix_Delta_last] using
          overlap_delta t (nextEpoch_subset_overlap p htEpoch)
    | cast j =>
        intro t ht
        by_cases hj : j = Fin.last p.i
        · subst j
          simpa only [SurgeryParameterPrefix.nextPrefix_Delta_penultimate] using
            overlap_delta t (lastEntry_subset_overlap p ht.2)
        · have hjlt : j.val < p.i := by
            have hjle := Nat.le_of_lt_succ j.isLt
            have hjne : j.val ≠ p.i := fun heq => hj (Fin.ext heq)
            omega
          rw [SurgeryParameterPrefix.nextPrefix_Delta_castSucc_of_lt p Q R j hjlt]
          exact old.delta_bound j (Nat.le_of_lt_succ j.isLt) t ht
  · change ∀ j : Fin ((p.i + 1) + 1), j.val ≤ p.i + 1 →
      ∀ t ∈ surgeryObservationInterval O ∩ surgeryEpochEntry j.val,
        F.parameters.r t = (p.nextPrefix Q R).r j
    intro j _hj
    cases j using Fin.lastCases with
    | last =>
        intro t ht
        have htEpoch : t ∈ surgeryEpoch p.i := by
          simpa [surgeryEpochEntry, surgeryEpoch] using ht.2
        simpa only [SurgeryParameterPrefix.nextPrefix_r_last] using next_r t htEpoch
    | cast j =>
        simpa only [Fin.val_castSucc, SurgeryParameterPrefix.nextPrefix_r_castSucc]
          using old.r_schedule j (Nat.le_of_lt_succ j.isLt)
  · change ∀ j : Fin ((p.i + 1) + 1), j.val ≤ p.i + 1 →
      ∀ t ∈ surgeryObservationInterval O ∩ surgeryEpochEntry j.val,
        F.parameters.kappa t = (p.nextPrefix Q R).kappa j
    intro j _hj
    cases j using Fin.lastCases with
    | last =>
        intro t ht
        have htEpoch : t ∈ surgeryEpoch p.i := by
          simpa [surgeryEpochEntry, surgeryEpoch] using ht.2
        simpa only [SurgeryParameterPrefix.nextPrefix_kappa_last] using
          next_kappa t htEpoch
    | cast j =>
        simpa only [Fin.val_castSucc, SurgeryParameterPrefix.nextPrefix_kappa_castSucc]
          using old.kappa_schedule j (Nat.le_of_lt_succ j.isLt)
  · intro j _hj
    cases j using Fin.lastCases with
    | last =>
        intro t ht
        have htEpoch : t ∈ surgeryEpoch p.i := by
          simpa [surgeryEpochEntry, surgeryEpoch] using ht.2
        exact next_h t htEpoch
    | cast j =>
        exact old.h_schedule j (Nat.le_of_lt_succ j.isLt)

theorem SurgeryPrefixControls.noncollapsedAssumptionOn
    {K : MetricSurgeryConstants} {p : SurgeryParameterPrefix K}
    {Q : SurgeryNoncollapseExtension.{u} p}
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (old : SurgeryPrefixControls p F O)
    (hnext : SurgeryObservationIsNextEpoch p O)
    (noncollapsed : SurgeryNoncollapsedOn F (surgeryObservationInterval O)
      Q.kappaNew)
    (next_kappa : ∀ t ∈ surgeryEpoch p.i,
      F.parameters.kappa t = Q.kappaNew) :
    SurgeryNoncollapsedAssumptionOn F (surgeryObservationInterval O) := by
  intro t ht htF x hx r hr hre e hzero hcurv
  by_cases hnew : t ∈ surgeryEpoch p.i
  · have hv := noncollapsed t ht htF x hx r hr hre e hzero hcurv
    simpa [next_kappa t hnew] using hv
  · have ht0 : 0 ≤ t := ht.1
    have htH : t < O.H := ht.2
    have hti : t < surgeryEpochStart p.i := by
      by_contra hnot
      have hti' : surgeryEpochStart p.i ≤ t := le_of_not_gt hnot
      have hnext' : t < surgeryEpochStart (p.i + 1) :=
        lt_of_lt_of_le htH hnext.2
      exact hnew ⟨hti', hnext'⟩
    obtain ⟨j, hj⟩ := epochEntry_exists p.i ht0 hti
    have hjold : j.val ≤ p.i := Nat.le_of_lt_succ j.isLt
    have hjobs : t ∈ surgeryObservationInterval O ∩ surgeryEpochEntry j.val :=
      ⟨ht, hj⟩
    have hv := old.noncollapsed j hjold t hjobs htF x hx r hr hre e hzero hcurv
    have hk := old.kappa_schedule j hjold t hjobs
    simpa [hk] using hv

theorem SurgeryPrefixControls.nextPrefix_of_extension
    {K : MetricSurgeryConstants} {p : SurgeryParameterPrefix K}
    {Q : SurgeryNoncollapseExtension.{u} p} {R : SurgeryCanonicalExtension p Q}
    {F : SurgeryFlowData.{u}} (E : SurgeryFlowExtension F)
    {O : SurgeryObservation E.extended}
    (old : SurgeryPrefixControls p E.extended O)
    (canonical : SurgeryCanonicalOn E.extended (surgeryObservationInterval O) R.rNext)
    (noncollapsed : SurgeryNoncollapsedOn E.extended
      (surgeryObservationInterval O) Q.kappaNew)
    (next_r : ∀ t ∈ surgeryEpoch p.i, F.parameters.r t = R.rNext)
    (next_kappa : ∀ t ∈ surgeryEpoch p.i,
      F.parameters.kappa t = Q.kappaNew)
    (next_h : ∀ t ∈ surgeryEpoch p.i,
      F.parameters.h t = p.setup.selector.h
        (F.parameters.delta t * F.parameters.r t) (F.parameters.delta t))
    (overlap_delta : ∀ t ∈ overlapInterval p, F.parameters.delta t ≤ R.deltaNext) :
    SurgeryPrefixControls (p.nextPrefix Q R) E.extended O := by
  apply old.nextPrefix canonical noncollapsed
  · simpa only [E.parameters_eq] using next_r
  · simpa only [E.parameters_eq] using next_kappa
  · simpa only [E.parameters_eq] using next_h
  · simpa only [E.parameters_eq] using overlap_delta

theorem RepairedEpochExtensionData.nextPrefix_with_derivative
    {S : RepairedControlledSchedulesData.{u}}
    {N : RepairedNoncollapseInductionData S}
    {C : RepairedCanonicalInductionData S N}
    (D : RepairedEpochExtensionData S N C)
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    (F : SurgeryFlowData.{u}) (O : SurgeryObservation F)
    (hstart : surgeryEpochStart p.i ≤ O.H)
    (hend : O.H < surgeryEpochStart (p.i + 1))
    (hdomain : F.time_domain = Set.Ico 0 O.H)
    (slab : RepairedPreterminalSlab F O.H)
    (old : SurgeryPrefixControls p F O)
    (terminal_policy : SurgeryFlowTerminalPolicyOn F (surgeryObservationInterval O))
    (controls : SurgeryEpochContinuationControls p F O
      (Classical.choice (N.induction p hp))
      (Classical.choice (C.induction p hp)))
    (r A : ℝ)
    (derivative : ∀ (E : SurgeryFlowExtension F)
      (O' : SurgeryObservation E.extended),
      SurgeryScalarDerivativeControlOn E.extended
        (surgeryObservationInterval O')
        r A) :
    ∃ (E : SurgeryFlowExtension F) (O' : SurgeryObservation E.extended),
      O.H < O'.H ∧ O'.H ≤ surgeryEpochStart (p.i + 1) ∧
        SurgeryPrefixControls
          (p.nextPrefix (Classical.choice (N.induction p hp))
            (Classical.choice (C.induction p hp))) E.extended O' ∧
        (∀ t ∈ surgeryEpoch p.i,
          E.extended.parameters.kappa t =
            (Classical.choice (N.induction p hp)).kappaNew) ∧
        SurgeryScalarDerivativeControlOn E.extended (surgeryObservationInterval O')
          r A := by
  obtain ⟨E, _old_event_data, _terminal_policy, O', hprogress, hbound,
      _hsurgery, _hfree, _hfrontier, _hinterval,
      returned_old, _hadmissible, _hpinched, _hstandard,
      hnextkappa, hcanonical, hnoncollapsed, _hexcluded_frontier⟩ :=
    D.extension_progress p hp F O hstart hend hdomain slab old terminal_policy controls
  exact ⟨E, O', hprogress, hbound,
    returned_old.nextPrefix_of_extension E hcanonical hnoncollapsed
      controls.next_r controls.next_kappa controls.next_h controls.overlap_delta,
      hnextkappa,
      derivative E O'⟩

theorem RepairedEpochExtensionData.nextPrefix
    {S : RepairedControlledSchedulesData.{u}}
    {N : RepairedNoncollapseInductionData S}
    {C : RepairedCanonicalInductionData S N}
    (D : RepairedEpochExtensionData S N C)
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    (F : SurgeryFlowData.{u}) (O : SurgeryObservation F)
    (hstart : surgeryEpochStart p.i ≤ O.H)
    (hend : O.H < surgeryEpochStart (p.i + 1))
    (hdomain : F.time_domain = Set.Ico 0 O.H)
    (slab : RepairedPreterminalSlab F O.H)
    (old : SurgeryPrefixControls p F O)
    (terminal_policy : SurgeryFlowTerminalPolicyOn F (surgeryObservationInterval O))
    (controls : SurgeryEpochContinuationControls p F O
      (Classical.choice (N.induction p hp))
      (Classical.choice (C.induction p hp))) :
    ∃ (E : SurgeryFlowExtension F) (O' : SurgeryObservation E.extended),
      O.H < O'.H ∧ O'.H ≤ surgeryEpochStart (p.i + 1) ∧
        SurgeryPrefixControls
          (p.nextPrefix (Classical.choice (N.induction p hp))
            (Classical.choice (C.induction p hp))) E.extended O' ∧
        (∀ t ∈ surgeryEpoch p.i,
          E.extended.parameters.kappa t =
            (Classical.choice (N.induction p hp)).kappaNew) := by
  obtain ⟨E, _old_event_data, _terminal_policy, O', hprogress, hbound,
      _hsurgery, _hfree, _hfrontier, _hinterval,
      returned_old, _hadmissible, _hpinched, _hstandard,
      hnextkappa, hcanonical, hnoncollapsed, _hexcluded_frontier⟩ :=
    D.extension_progress p hp F O hstart hend hdomain slab old terminal_policy controls
  exact ⟨E, O', hprogress, hbound,
    returned_old.nextPrefix_of_extension E hcanonical hnoncollapsed
      controls.next_r controls.next_kappa controls.next_h controls.overlap_delta,
      hnextkappa⟩

theorem SurgeryPrefixControls.canonicalAssumptionOn
    {K : MetricSurgeryConstants} {p : SurgeryParameterPrefix K}
    {Q : SurgeryNoncollapseExtension.{u} p} {R : SurgeryCanonicalExtension p Q}
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (old : SurgeryPrefixControls p F O)
    (horizon_le : O.H ≤ surgeryEpochStart (p.i + 1))
    (canonical : SurgeryCanonicalOn F (surgeryObservationInterval O) R.rNext)
    (next_r : ∀ t ∈ surgeryEpoch p.i, F.parameters.r t = R.rNext) :
    ∀ t ∈ surgeryObservationInterval O, ∀ _htF : t ∈ F.time_domain,
      ∀ x : (F.slice t).carrier,
        (F.parameters.r t)⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature x →
          SurgeryCanonicalControl F t x F.parameters.epsilon F.parameters.C := by
  intro t ht htF x hx
  by_cases hnew : t ∈ surgeryEpoch p.i
  · exact canonical t ht htF x (by simpa only [next_r t hnew] using hx)
  · have hti : t < surgeryEpochStart p.i := by
      by_contra hnot
      exact hnew ⟨le_of_not_gt hnot, ht.2.trans_le horizon_le⟩
    obtain ⟨j, hj⟩ := epochEntry_exists p.i ht.1 hti
    have hjold : j.val ≤ p.i := Nat.le_of_lt_succ j.isLt
    have hjobs : t ∈ surgeryObservationInterval O ∩ surgeryEpochEntry j.val := ⟨ht, hj⟩
    exact old.canonical j hjold t hjobs htF x
      (by simpa only [old.r_schedule j hjold t hjobs] using hx)

end PoincareConjecture
