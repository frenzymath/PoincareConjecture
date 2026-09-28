import PoincareConjecture.Definitions.Ch16.NoncollapseInduction
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Prop16_1_Prefix

set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture

theorem SurgeryCanonicalOn.restrict
    {F : SurgeryFlowData.{u}} {I J : Set ℝ} {r : ℝ}
    (h : SurgeryCanonicalOn F I r) (hJI : J ⊆ I) :
    SurgeryCanonicalOn F J r := by
  intro t ht
  exact h t (hJI ht)

theorem SurgeryCanonicalOn.mono_radius
    {F : SurgeryFlowData.{u}} {J : Set ℝ} {r rSmall : ℝ}
    (h : SurgeryCanonicalOn F J r) (hr : 0 < rSmall) (hle : rSmall ≤ r) :
    SurgeryCanonicalOn F J rSmall := by
  have hr' : 0 < r := hr.trans_le hle
  have hinv : r⁻¹ ≤ rSmall⁻¹ := (inv_le_inv₀ hr' hr).2 hle
  have hpow : r⁻¹ ^ 2 ≤ rSmall⁻¹ ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr hr'.le) hinv 2
  intro t ht htF x hscalar
  exact h t ht htF x (hpow.trans hscalar)

theorem SurgeryPrefixControls.canonicalOn_prefixFinal
    {K : MetricSurgeryConstants} {p : SurgeryParameterPrefix K}
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (h : SurgeryPrefixControls p F O) {rNext : ℝ} (hr : 0 < rNext)
    (hle : rNext ≤ p.r (Fin.last p.i)) :
    SurgeryCanonicalOn F (surgeryObservationInterval O ∩ prefixFinalInterval p) rNext := by
  intro t ht htF x hscalar
  obtain ⟨j, hj⟩ := Proofs.M46.exists_epochEntry p.i ht.2
  have hjlast : j.val ≤ p.i := Nat.le_of_lt_succ j.isLt
  have hrj : rNext ≤ p.r j :=
    hle.trans (p.r_antitone (show j.val ≤ (Fin.last p.i).val from hjlast))
  exact (h.canonical j hjlast).mono_radius hr hrj t ⟨ht.1, hj⟩ htF x hscalar

theorem SurgeryObservation.interval_subset_of_horizon_le
    {F : SurgeryFlowData.{u}} {Osmall Olarge : SurgeryObservation F}
    (hH : Osmall.H ≤ Olarge.H) :
    surgeryObservationInterval Osmall ⊆ surgeryObservationInterval Olarge := by
  intro t ht
  exact ⟨ht.1, ht.2.trans_le hH⟩

def SurgeryObservation.restrictTo {F : SurgeryFlowData.{u}}
    (O : SurgeryObservation F) (H : ℝ) (hH : 0 < H) (hle : H ≤ O.H) :
    SurgeryObservation F where
  H := H
  H_pos := hH
  interval_subset := fun _ ht => O.interval_subset ⟨ht.1, ht.2.trans_le hle⟩
  standard_flow := O.standard_flow

theorem SurgeryPrefixControls.restrictObservation
    {K : MetricSurgeryConstants} {p : SurgeryParameterPrefix K}
    {F : SurgeryFlowData.{u}} {Osmall Olarge : SurgeryObservation F}
    (h : SurgeryPrefixControls p F Olarge) (hH : Osmall.H ≤ Olarge.H) :
    SurgeryPrefixControls p F Osmall := by
  have hJ := SurgeryObservation.interval_subset_of_horizon_le hH
  exact {
    standard_initial_eq := h.standard_initial_eq
    local_constants_eq := h.local_constants_eq
    epsilon_eq := h.epsilon_eq
    C_eq := h.C_eq
    admissible := h.admissible
    pinched := fun t ht => h.pinched t (hJ ht)
    canonical := fun j hj t ht => h.canonical j hj t ⟨hJ ht.1, ht.2⟩
    noncollapsed := fun j hj t ht => h.noncollapsed j hj t ⟨hJ ht.1, ht.2⟩
    delta_bound := fun j hj t ht => h.delta_bound j hj t ⟨hJ ht.1, ht.2⟩
    r_schedule := fun j hj t ht => h.r_schedule j hj t ⟨hJ ht.1, ht.2⟩
    kappa_schedule := fun j hj t ht => h.kappa_schedule j hj t ⟨hJ ht.1, ht.2⟩
    h_schedule := fun j hj t ht => h.h_schedule j hj t ⟨hJ ht.1, ht.2⟩ }

theorem SurgeryPostPrefixScales.restrictObservation
    {K : MetricSurgeryConstants} {p : SurgeryParameterPrefix K}
    {F : SurgeryFlowData.{u}} {Osmall Olarge : SurgeryObservation F}
    {rNext deltaNext : ℝ} (h : SurgeryPostPrefixScales p F Olarge rNext deltaNext)
    (hH : Osmall.H ≤ Olarge.H) :
    SurgeryPostPrefixScales p F Osmall rNext deltaNext := by
  have hJ := SurgeryObservation.interval_subset_of_horizon_le hH
  exact {
    r_eq := fun t ht => h.r_eq t ⟨hJ ht.1, ht.2⟩
    delta_le := fun t ht => h.delta_le t ⟨hJ ht.1, ht.2⟩
    h_eq := fun t ht => h.h_eq t ⟨hJ ht.1, ht.2⟩ }

theorem SurgeryPostPrefixScales.mono_delta
    {K : MetricSurgeryConstants} {p : SurgeryParameterPrefix K}
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    {rNext deltaSmall deltaLarge : ℝ}
    (h : SurgeryPostPrefixScales p F O rNext deltaSmall)
    (hle : deltaSmall ≤ deltaLarge) :
    SurgeryPostPrefixScales p F O rNext deltaLarge where
  r_eq := h.r_eq
  delta_le := fun t ht => (h.delta_le t ht).trans hle
  h_eq := h.h_eq

theorem SurgeryFlowTerminalPolicyOn.restrictObservation
    {F : SurgeryFlowData.{u}} {Osmall Olarge : SurgeryObservation F}
    (h : SurgeryFlowTerminalPolicyOn F (surgeryObservationInterval Olarge))
    (hH : Osmall.H ≤ Olarge.H) :
    SurgeryFlowTerminalPolicyOn F (surgeryObservationInterval Osmall) :=
  SurgeryFlowTerminalPolicyOn.restrict
    (SurgeryObservation.interval_subset_of_horizon_le hH) h

theorem SurgeryObservationIsNextEpoch.restrictObservation
    {K : MetricSurgeryConstants} {p : SurgeryParameterPrefix K}
    {F : SurgeryFlowData.{u}} {Osmall Olarge : SurgeryObservation F}
    (h : SurgeryObservationIsNextEpoch p Olarge) (hH : Osmall.H ≤ Olarge.H)
    (hstart : surgeryEpochStart p.i < Osmall.H) :
    SurgeryObservationIsNextEpoch p Osmall :=
  ⟨hstart, hH.trans h.2⟩

theorem SurgeryPrefixControls.noncollapsedOn_before_prefixEnd
    {K : MetricSurgeryConstants} {p : SurgeryParameterPrefix K}
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (h : SurgeryPrefixControls p F O) (hH : surgeryEpochStart p.i ≤ O.H)
    {kappa : ℝ} (hle : kappa ≤ p.kappa (Fin.last p.i)) :
    SurgeryNoncollapsedOn F (Ico 0 (surgeryEpochStart p.i)) kappa := by
  intro t ht
  exact Proofs.M46.prefix_noncollapsed h hle t ⟨⟨ht.1, ht.2.trans_le hH⟩, ht⟩

end PoincareConjecture
