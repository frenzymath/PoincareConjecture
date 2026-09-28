import PoincareConjecture.Proofs.M33.SurgeryCylinderRestriction
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_RemovalSurvival
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_TrackedBall










set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.M47



theorem cap_not_disappears_of_surviving_cylinder
    {F : SurgeryFlowData.{u}} {origin scale c d : ℝ}
    {U V : Set (F.slice origin).carrier}
    (e : SurgeryFlowCylinder F (F.slice origin) origin scale (Ico 0 c) U)
    (f : SurgeryFlowCylinder F (F.slice origin) origin scale (Icc 0 d) V)
    (hc : 0 < c) (hcd : c < d) (y : (F.slice origin).carrier)
    (hyU : y ∈ U) (hyV : y ∈ V)
    (hinitial : ∀ h x, x ∈ V → HEq (f.forward 0 h x) x) :
    ¬ SurgeryBallDisappearsAt F e (origin + c / scale) := by
  let inner := f.restrict (Ico_subset_Icc_self : Ico 0 d ⊆ Icc 0 d)
    ordConnected_Ico (inter_subset_left : V ∩ U ⊆ V)
  exact M44.not_disappears_of_surviving_subcylinder e inner hc hcd
    inter_subset_right ⟨y, hyV, hyU⟩ (fun h x hx => hinitial _ x hx.1)



theorem inserted_cap_subset_persistence_ball
    {F : SurgeryFlowData.{u}} {t A : ℝ} (hT : t ∈ F.surgery_times)
    [Nonempty (F.slice t).carrier] (i : Fin (F.event t hT).cap_count)
    (hA : F.standard_initial.cylindrical_end.radius + 5 < A) :
    ((F.event t hT).caps i).carrier ⊆
      (F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t) := by
  have hApos : 0 < A := by linarith [F.standard_initial.cylindrical_end.radius_pos]
  have hh : 0 < F.parameters.h t :=
    F.parameters.h_pos t (F.time_domain_nonnegative (F.surgery_times_subset hT))
  intro y hy
  have houter := ((F.event t hT).caps i).outer_ball hy
  change (F.metric t).edist ((F.event t hT).caps i).tip y <
    ENNReal.ofReal (A * F.parameters.h t)
  apply houter.trans_lt
  apply (ENNReal.ofReal_lt_ofReal_iff (mul_pos hApos hh)).mpr
  nlinarith



theorem cap_persistence_of_surviving_birth_cylinder
    {F : SurgeryFlowData.{u}} (O : SurgeryObservation F)
    {t A eta theta : ℝ} (hT : t ∈ F.surgery_times)
    [Nonempty (F.slice t).carrier] (i : Fin (F.event t hT).cap_count)
    (hA : F.standard_initial.cylindrical_end.radius + 5 < A)
    (V : Set (F.slice t).carrier)
    (f : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2)
      (Icc 0 ((O.H - t) / (F.parameters.h t) ^ 2)) V)
    (hinitial : ∀ h x, x ∈ V → HEq (f.forward 0 h x) x)
    (y : (F.slice t).carrier) (hyV : y ∈ V)
    (hycap : y ∈ ((F.event t hT).caps i).carrier)
    (hpersist : SurgeryCapPersistenceAlternative F O t hT i A eta theta) :
    ∃ e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2)
        (Ico 0 (surgeryCapDuration t O.H (F.parameters.h t) theta))
        ((F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t)),
      ∃ initial : SurgeryCapInitialComparison F t hT i A,
        SurgeryCapFamilyComparison F O.standard_flow A eta e initial.chart ∧
        ∀ h x, x ∈ (F.metric t).ball ((F.event t hT).caps i).tip
          (A * F.parameters.h t) → HEq (e.forward 0 h x) x := by
  rcases hpersist with hfirst |
    ⟨top, httop, _hTop, htop, e, _initial, _comparison, _based, hdisappears⟩
  · exact hfirst
  · have hh : 0 < F.parameters.h t :=
      F.parameters.h_pos t (F.time_domain_nonnegative (F.surgery_times_subset hT))
    have hsq : 0 < (F.parameters.h t) ^ 2 := sq_pos_of_pos hh
    have hc : 0 < (top - t) / (F.parameters.h t) ^ 2 :=
      div_pos (sub_pos.mpr httop) hsq
    have hcd : (top - t) / (F.parameters.h t) ^ 2 <
        (O.H - t) / (F.parameters.h t) ^ 2 :=
      (div_lt_div_iff_of_pos_right hsq).mpr
        (sub_lt_sub_right (htop.trans_le (min_le_left _ _)) t)
    have hclock : t + ((top - t) / (F.parameters.h t) ^ 2) /
        ((F.parameters.h t)⁻¹ ^ 2) = top := by
      rw [surgeryCap_physical_time, div_mul_cancel₀ _ hsq.ne']
      ring
    have hnot := cap_not_disappears_of_surviving_cylinder e f hc hcd y
      (inserted_cap_subset_persistence_ball hT i hA hycap) hyV hinitial
    rw [hclock] at hnot
    exact (hnot hdisappears).elim

end PoincareConjecture.M47
