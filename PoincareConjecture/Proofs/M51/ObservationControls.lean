import PoincareConjecture.Proofs.M51.Parameters

set_option autoImplicit false

open Set
open scoped ENNReal

universe u

namespace PoincareConjecture

private theorem entry_time_lt {j : ℕ} {t : ℝ}
    (ht : t ∈ surgeryEpochEntry j) : t < surgeryEpochStart j := by
  by_cases hj : j = 0
  · subst j
    exact ht.2
  · exact (show t ∈ Ico (surgeryEpochStart (j - 1)) (surgeryEpochStart j) from
      by simpa [surgeryEpochEntry, hj] using ht).2

private theorem observed_old_entry {K : MetricSurgeryConstants}
    {p : SurgeryParameterPrefix K} {F : SurgeryFlowData.{u}}
    {O : SurgeryObservation F} (hH : O.H ≤ surgeryEpochStart p.i)
    {t : ℝ} (ht : t ∈ surgeryObservationInterval O) :
    ∃ j : Fin (p.i + 1), t ∈ surgeryEpochEntry j.val := by
  have hj := M51Numerical.epochIndex_le (ht.2.trans_le hH)
  exact ⟨⟨M51Numerical.epochIndex t, Nat.lt_succ_of_le hj⟩,
    M51Numerical.mem_epochEntry_index ht.1⟩

theorem SurgeryPrefixControls.observePastPrefix
    {K : MetricSurgeryConstants} {p : SurgeryParameterPrefix K}
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (old : SurgeryPrefixControls p F O) (O' : SurgeryObservation F)
    (hstart : surgeryEpochStart p.i ≤ O.H) (hpinched : SurgeryFlowPinched F) :
    SurgeryPrefixControls p F O' := by
  have htime {j : Fin (p.i + 1)} {t : ℝ}
      (ht : t ∈ surgeryObservationInterval O' ∩ surgeryEpochEntry j.val) :
      t ∈ surgeryObservationInterval O ∩ surgeryEpochEntry j.val := by
    refine ⟨⟨ht.1.1, ?_⟩, ht.2⟩
    exact (entry_time_lt ht.2).trans_le
      ((M51Numerical.epochStart_strictMono.monotone
        (Nat.le_of_lt_succ j.isLt)).trans hstart)
  exact {
    standard_initial_eq := old.standard_initial_eq
    local_constants_eq := old.local_constants_eq
    epsilon_eq := old.epsilon_eq
    C_eq := old.C_eq
    admissible := old.admissible
    pinched := fun t _ ht => hpinched t ht
    canonical := fun j hj t ht => old.canonical j hj t (htime ht)
    noncollapsed := fun j hj t ht => old.noncollapsed j hj t (htime ht)
    delta_bound := fun j hj t ht => old.delta_bound j hj t (htime ht)
    r_schedule := fun j hj t ht => old.r_schedule j hj t (htime ht)
    kappa_schedule := fun j hj t ht => old.kappa_schedule j hj t (htime ht)
    h_schedule := fun j hj t ht => old.h_schedule j hj t (htime ht) }

theorem SurgeryPrefixControls.canonicalBeforePrefix
    {K : MetricSurgeryConstants} {p : SurgeryParameterPrefix K}
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (old : SurgeryPrefixControls p F O) (hH : O.H ≤ surgeryEpochStart p.i)
    {Q : SurgeryNoncollapseExtension.{u} p} (R : SurgeryCanonicalExtension p Q) :
    SurgeryCanonicalOn F (surgeryObservationInterval O) R.rNext := by
  intro t ht htF x hx
  obtain ⟨j, hj⟩ := observed_old_entry hH ht
  have hji : j.val ≤ p.i := Nat.le_of_lt_succ j.isLt
  have hr : R.rNext ≤ p.r j := R.r_le_last.trans (p.r_antitone hji)
  have hinv : (p.r j)⁻¹ ≤ R.rNext⁻¹ := (inv_le_inv₀ (p.r_pos j) R.r_pos).2 hr
  have hsquare := pow_le_pow_left₀ (inv_nonneg.mpr (p.r_pos j).le) hinv 2
  exact old.canonical j hji t ⟨ht, hj⟩ htF x (hsquare.trans hx)

theorem SurgeryPrefixControls.noncollapsedBeforePrefix
    {K : MetricSurgeryConstants} {p : SurgeryParameterPrefix K}
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (old : SurgeryPrefixControls p F O) (hH : O.H ≤ surgeryEpochStart p.i)
    (Q : SurgeryNoncollapseExtension.{u} p) :
    SurgeryNoncollapsedOn F (surgeryObservationInterval O) Q.kappaNew := by
  intro t ht htF x hx r hr hre e hzero hcurv
  obtain ⟨j, hj⟩ := observed_old_entry hH ht
  have hji : j.val ≤ p.i := Nat.le_of_lt_succ j.isLt
  have hk : Q.kappaNew ≤ p.kappa j := Q.kappa_le_last.trans (p.kappa_antitone hji)
  exact (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hk (pow_nonneg hr.le 3))).trans
      (old.noncollapsed j hji t ⟨ht, hj⟩ htF x hx r hr hre e hzero hcurv)

theorem SurgeryPrefixControls.noncollapsedProfileBeforePrefix
    {K : MetricSurgeryConstants} {p : SurgeryParameterPrefix K}
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (old : SurgeryPrefixControls p F O) (hH : O.H ≤ surgeryEpochStart p.i) :
    SurgeryNoncollapsedAssumptionOn F (surgeryObservationInterval O) := by
  intro t ht htF x hx r hr hre e hzero hcurv
  obtain ⟨j, hj⟩ := observed_old_entry hH ht
  have hji : j.val ≤ p.i := Nat.le_of_lt_succ j.isLt
  have hv := old.noncollapsed j hji t ⟨ht, hj⟩ htF x hx r hr hre e hzero hcurv
  simpa only [old.kappa_schedule j hji t ⟨ht, hj⟩] using hv

end PoincareConjecture
