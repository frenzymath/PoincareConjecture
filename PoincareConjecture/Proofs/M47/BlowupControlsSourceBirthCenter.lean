import PoincareConjecture.Proofs.M47.CanonicalNeckCapTipDistance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

theorem exists_cap_birth_center_in_fixed_ball
    {F : SurgeryFlowData.{u}} {t : ℝ} {hT : t ∈ F.surgery_times}
    [Nonempty (F.slice t).carrier] {i : Fin (F.event t hT).cap_count}
    {S : MaximalStandardCapFlow F.standard_initial} {R A eta : ℝ}
    (hR : 0 < R) (hRA : R ≤ A) (heta : 0 < eta) (hetaSmall : eta ≤ 1 / 1000)
    {J : Set ℝ}
    (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J
      ((F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t)))
    (initial : SurgeryCapInitialComparison F t hT i A)
    (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
    (hzero : (0 : ℝ) ∈ J)
    (based : ∀ y ∈ (F.metric t).ball ((F.event t hT).caps i).tip
      (A * F.parameters.h t), HEq (e.forward 0 hzero y) y)
    {p : (F.slice t).carrier}
    (hp : p ∈ (F.metric t).ball ((F.event t hT).caps i).tip (R * F.parameters.h t)) :
    ∃ z ∈ F.standard_initial.metric.ball 0 A,
      initial.chart z = p ∧ F.standard_initial.metric.edist 0 z ≤ ENNReal.ofReal (2 * R) := by
  have hh : 0 < F.parameters.h t :=
    F.parameters.h_pos t (F.time_domain_nonnegative (F.surgery_times_subset hT))
  have hA : 0 < A := hR.trans_le hRA
  have hpA : p ∈ (F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t) :=
    hp.trans_le (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hRA hh.le))
  obtain ⟨z, hz, hzp⟩ := comparison.choose_spec.2.2.2.1.symm ▸ hpA
  have hd := Proofs.M47.cap_birth_tip_distance_near_one hA e initial comparison hzero based
    hh heta hetaSmall hz
  rw [hzp] at hd
  have hpReal : ((F.metric t).edist ((F.event t hT).caps i).tip p).toReal <
      R * F.parameters.h t := ENNReal.toReal_lt_of_lt_ofReal hp
  have hscaled : (F.parameters.h t)⁻¹ *
      ((F.metric t).edist ((F.event t hT).caps i).tip p).toReal < R := by
    have h := mul_lt_mul_of_pos_left hpReal (inv_pos.mpr hh)
    have hid : (F.parameters.h t)⁻¹ * (R * F.parameters.h t) = R := by field_simp
    rwa [hid] at h
  have hreal : (F.standard_initial.metric.edist 0 z).toReal ≤ 2 * R := by
    nlinarith only [hd, hscaled, hR]
  refine ⟨z, hz, hzp, ?_⟩
  rw [← ENNReal.ofReal_toReal (F.standard_initial.metric.edist_ne_top 0 z)]
  exact ENNReal.ofReal_le_ofReal hreal

end PoincareConjecture.M47
