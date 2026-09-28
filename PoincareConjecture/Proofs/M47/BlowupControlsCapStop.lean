import PoincareConjecture.Proofs.M47.BlowupControlsCapClock
import PoincareConjecture.Proofs.M47.BlowupControlsCapTime










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

universe u

namespace PoincareConjecture.M47

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  (O : SurgeryObservation F) {Q a : ℝ} {U : Set C.carrier}

local notation "birth" => O.H + a / Q



theorem cap_stop_elapsed_lt_comparison_margin
    (e : SurgeryFlowCylinder F C O.H Q (Icc a 0) U)
    (hU : IsOpen U) (ha : a < 0)
    (hT : birth ∈ F.surgery_times) [Nonempty (F.slice birth).carrier]
    (i : Fin (F.event birth hT).cap_count)
    {A eta theta1 theta2 c T D : ℝ}
    (hA : F.standard_initial.cylindrical_end.radius + 5 < A) (hD : 0 ≤ D)
    (htheta1 : 1 / 2 < theta1) (htheta12 : theta1 < theta2) (htheta2 : theta2 < 1)
    (hrate : 2 * T * D < c / (2 * (1 - (2 * theta1 - 1)))) (helapsed : -a ≤ T)
    (x : C.carrier) (hx : x ∈ U)
    (hycap : e.forward a ⟨le_rfl, ha.le⟩ x ∈ ((F.event birth hT).caps i).carrier)
    (hscalar : ∀ s (hs : s ∈ Icc a 0),
      (F.connection (O.H + s / Q)).scalarCurvature (e.forward s hs x) ≤ D * Q)
    (hbound : ∀ (J : Set ℝ) (V : Set (F.slice birth).carrier)
      (d : SurgeryFlowCylinder F (F.slice birth) birth
        ((F.parameters.h birth)⁻¹ ^ 2) J V)
      (initial : SurgeryCapInitialComparison F birth hT i A),
      SurgeryCapFamilyComparison F O.standard_flow A eta d initial.chart →
      ∀ (s : ℝ) (hs : s ∈ J), s ≤ theta2 →
      ∀ z ∈ F.standard_initial.metric.ball 0 A,
        c / (2 * (1 - s) * (F.parameters.h birth) ^ 2) ≤
          (F.connection (birth + s / ((F.parameters.h birth)⁻¹ ^ 2))).scalarCurvature
            (d.forward s hs (initial.chart z)))
    (hpersist : SurgeryCapPersistenceAlternative F O birth hT i A eta theta2) :
    -a < theta1 * (Q * (F.parameters.h birth) ^ 2) := by
  have hQ : 0 < Q := e.scale_pos
  have htH : birth < O.H := by linarith only [div_neg_of_neg_of_pos ha hQ]
  have hclock : Q * (O.H - birth) = -a := by
    field_simp [hQ.ne']
    ring
  have hh : 0 < F.parameters.h birth :=
    F.parameters.h_pos birth (F.time_domain_nonnegative (F.surgery_times_subset hT))
  obtain ⟨f, based, scalar⟩ :=
    exists_cap_birth_cylinder_scalar_bound e hU ha (F.parameters.h birth) hh x hx hscalar
  have hmargin := cap_elapsed_lt_comparison_margin O hT i hA htH hQ hD
    htheta1 htheta12 htheta2 hrate (by rw [hclock]; exact helapsed)
    (e.forward a ⟨le_rfl, ha.le⟩ '' U) f based (e.forward a ⟨le_rfl, ha.le⟩ x)
    (mem_image_of_mem _ hx) hycap scalar hbound hpersist
  simpa only [hclock] using hmargin

end PoincareConjecture.M47
