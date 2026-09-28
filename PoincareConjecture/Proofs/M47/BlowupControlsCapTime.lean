import PoincareConjecture.Proofs.M47.BlowupControlsCapSurvival
import PoincareConjecture.Proofs.M47.BlowupControlsCapMargin

set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.M47

theorem cap_elapsed_lt_comparison_margin
    {F : SurgeryFlowData.{u}} (O : SurgeryObservation F)
    {t A eta theta1 theta2 c Q T D : ℝ} (hT : t ∈ F.surgery_times)
    [Nonempty (F.slice t).carrier] (i : Fin (F.event t hT).cap_count)
    (hA : F.standard_initial.cylindrical_end.radius + 5 < A)
    (htH : t < O.H) (hQ : 0 < Q) (hD : 0 ≤ D)
    (htheta1 : 1 / 2 < theta1) (htheta12 : theta1 < theta2)
    (htheta2 : theta2 < 1)
    (hrate : 2 * T * D < c / (2 * (1 - (2 * theta1 - 1))))
    (helapsed : Q * (O.H - t) ≤ T)
    (V : Set (F.slice t).carrier)
    (f : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2)
      (Icc 0 ((O.H - t) / (F.parameters.h t) ^ 2)) V)
    (hinitial : ∀ h x, x ∈ V → HEq (f.forward 0 h x) x)
    (y : (F.slice t).carrier) (hyV : y ∈ V)
    (hycap : y ∈ ((F.event t hT).caps i).carrier)
    (hscalar : ∀ s (hs : s ∈ Icc 0 ((O.H - t) / (F.parameters.h t) ^ 2)),
      (F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2))).scalarCurvature
        (f.forward s hs y) ≤ D * Q)
    (hbound : ∀ (J : Set ℝ) (U : Set (F.slice t).carrier)
      (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
      (initial : SurgeryCapInitialComparison F t hT i A),
      SurgeryCapFamilyComparison F O.standard_flow A eta e initial.chart →
      ∀ (s : ℝ) (hs : s ∈ J), s ≤ theta2 →
      ∀ x ∈ F.standard_initial.metric.ball 0 A,
        c / (2 * (1 - s) * (F.parameters.h t) ^ 2) ≤
          (F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2))).scalarCurvature
            (e.forward s hs (initial.chart x)))
    (hpersist : SurgeryCapPersistenceAlternative F O t hT i A eta theta2) :
    Q * (O.H - t) < theta1 * (Q * (F.parameters.h t) ^ 2) := by
  have hh : 0 < F.parameters.h t :=
    F.parameters.h_pos t (F.time_domain_nonnegative (F.surgery_times_subset hT))
  have hsq : 0 < (F.parameters.h t) ^ 2 := sq_pos_of_pos hh
  have hzeroF : (0 : ℝ) ∈ Icc 0 ((O.H - t) / (F.parameters.h t) ^ 2) :=
    ⟨le_rfl, (div_pos (sub_pos.mpr htH) hsq).le⟩
  obtain ⟨e, initial, comparison, based⟩ :=
    cap_persistence_of_surviving_birth_cylinder O hT i hA V f hinitial y hyV hycap hpersist
  have hyU := inserted_cap_subset_persistence_ball hT i hA hycap
  apply cap_elapsed_lt_time_margin hD (mul_pos hQ hsq) helapsed htheta1 hrate
  intro hlong
  let sigma := 2 * theta1 - 1
  have hsigma : 0 < sigma := by dsimp only [sigma]; linarith
  have hsigma1 : sigma < theta1 := by dsimp only [sigma]; linarith
  have hbase : theta1 * (F.parameters.h t) ^ 2 ≤ O.H - t := by
    apply (mul_le_mul_iff_left₀ hQ).mp
    nlinarith only [hlong]
  have hbefore : sigma * (F.parameters.h t) ^ 2 < O.H - t :=
    (mul_lt_mul_of_pos_right hsigma1 hsq).trans_le hbase
  have hsigmae : sigma ∈ Ico 0 (surgeryCapDuration t O.H (F.parameters.h t) theta2) := by
    refine ⟨hsigma.le, (lt_div_iff₀ hsq).mpr ?_⟩
    have hend : t + sigma * (F.parameters.h t) ^ 2 <
        min O.H (t + theta2 * (F.parameters.h t) ^ 2) :=
      lt_min (by linarith only [hbefore])
        (by linarith only [mul_lt_mul_of_pos_right (hsigma1.trans htheta12) hsq])
    change sigma * (F.parameters.h t) ^ 2 <
      min O.H (t + theta2 * (F.parameters.h t) ^ 2) - t
    linarith only [hend]
  have hsigmaf : sigma ∈ Icc 0 ((O.H - t) / (F.parameters.h t) ^ 2) :=
    ⟨hsigma.le, ((lt_div_iff₀ hsq).mpr hbefore).le⟩
  have heq : e.forward sigma hsigmae y = f.forward sigma hsigmaf y := by
    apply M44.cylinder_forward_eq_of_initial e f hsigma.le
      (fun _ hz => ⟨hz.1, hz.2.trans_lt hsigmae.2⟩)
      (fun _ hz => ⟨hz.1, hz.2.trans hsigmaf.2⟩) y hyU hyV
    exact eq_of_heq ((based _ y hyU).trans (hinitial hzeroF y hyV).symm)
  have himage : initial.chart '' F.standard_initial.metric.ball 0 A =
      (F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t) :=
    comparison.choose_spec.2.2.2.1
  obtain ⟨z, hz, hzy⟩ := himage.symm ▸ hyU
  have hlower := hbound _ _ e initial comparison sigma hsigmae
    (hsigma1.trans htheta12).le z hz
  rw [hzy, heq] at hlower
  let R := (F.connection (t + sigma / ((F.parameters.h t)⁻¹ ^ 2))).scalarCurvature
    (f.forward sigma hsigmaf y)
  have hR : R / Q ≤ D := (div_le_iff₀ hQ).mpr (hscalar sigma hsigmaf)
  have hlower' : c / (2 * (1 - sigma)) ≤ (F.parameters.h t) ^ 2 * R := by
    rw [div_mul_eq_div_div] at hlower
    have h := (div_le_iff₀ hsq).mp hlower
    simpa only [mul_comm] using h
  refine ⟨R / Q, hR, ?_⟩
  change c / (2 * (1 - sigma)) ≤ (Q * (F.parameters.h t) ^ 2) * (R / Q)
  have hnormalize : (Q * (F.parameters.h t) ^ 2) * (R / Q) =
      (F.parameters.h t) ^ 2 * R := by
    field_simp
  rw [hnormalize]
  exact hlower'

end PoincareConjecture.M47
