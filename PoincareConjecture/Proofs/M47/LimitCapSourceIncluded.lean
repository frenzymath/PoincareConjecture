import PoincareConjecture.Proofs.M47.LimitCapSourceBirth
import PoincareConjecture.Proofs.M47.LimitCapSourceCapture
import PoincareConjecture.Proofs.M47.BlowupControlsCapIncluded
import PoincareConjecture.Proofs.M47.BlowupControlsCapStop
import PoincareConjecture.Proofs.M47.BlowupControlsCapScalar
import PoincareConjecture.Proofs.M47.CanonicalNeckCapReclock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

open Proofs.M46

theorem exists_finite_source_included_cap_comparison_cutoff
    (P : M44CapPersistencePredecessors.{u}) {g0 : StandardInitialMetric}
    (standard : RepairedStandardCapExistenceData g0)
    {T K D c : ℝ} (hT : 0 ≤ T) (hK : 0 < K) (hD : 0 ≤ D) (hc : 0 < c) :
    ∃ theta1 theta2 Rcap : ℝ,
      1 / 2 < theta1 ∧ theta1 < theta2 ∧ theta2 < 1 ∧
      g0.cylindrical_end.radius + 5 < Rcap ∧
      ∀ Rrequested : ℝ, ∃ A eta0 delta0 : ℝ,
        Rrequested < A ∧ Rcap < A ∧
        g0.cylindrical_end.radius + 5 < A ∧ 0 < eta0 ∧ eta0 ≤ 1 / 2 ∧
        0 < delta0 ∧
        ∀ (F : SurgeryFlowData.{u}), F.standard_initial = g0 →
        ∀ (O Oambient : SurgeryObservation F), HEq O.standard_flow standard.flow →
          SurgeryFlowPinched F →
        ∀ {constants : MetricSurgeryConstants} (setup : SurgeryControlSetup constants)
          {start rNext deltaBar : ℝ},
          SurgeryFixedScalesOn setup F Oambient start rNext deltaBar → deltaBar ≤ delta0 →
          O.H ∈ surgeryObservationInterval Oambient ∩ Ici start →
        ∀ (C : GeneralizedSliceCarrier.{u}) {U : Set C.carrier} (_hU : IsOpen U)
          {Q a : ℝ} (ha : a ∈ Ico (-T) 0),
        ∀ E : SurgeryFlowCylinder F C O.H Q (Icc a 0) U,
          (∀ s (hs : s ∈ Icc a 0), ∀ x ∈ U,
            (F.connection (O.H + s / Q)).scalarCurvature (E.forward s hs x) ≤ K * Q) →
          let bottom : a ∈ Icc a 0 := ⟨le_rfl, ha.2.le⟩
          let t := O.H + a / Q
          let d := (O.H - t) / (F.parameters.h t) ^ 2
          ∀ (hEvent : t ∈ F.surgery_times), ∀ [Nonempty (F.slice t).carrier],
          ∀ (i : Fin (F.event t hEvent).cap_count) (contact : C.carrier),
            contact ∈ U → E.forward a bottom contact ∈ ((F.event t hEvent).caps i).carrier →
            (∀ x ∈ U, (F.metric t).edist (E.forward a bottom contact)
              (E.forward a bottom x) ≤ ENNReal.ofReal (D / Real.sqrt Q)) →
            (F.parameters.h t) ^ 2 ≤ 1 →
          ∀ eta : ℝ, 0 < eta → eta ≤ eta0 →
            (∀ (J : Set ℝ) (V : Set (F.slice t).carrier)
              (f : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J V)
              (initial : SurgeryCapInitialComparison F t hEvent i A),
              SurgeryCapFamilyComparison F O.standard_flow A eta f initial.chart →
              ∀ (s : ℝ) (hs : s ∈ J), s ≤ theta2 →
              ∀ z ∈ F.standard_initial.metric.ball 0 A,
                c / (2 * (1 - s) * (F.parameters.h t) ^ 2) ≤
                  (F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2))).scalarCurvature
                    (f.forward s hs (initial.chart z))) →
            SurgeryCapPersistenceAlternative F O t hEvent i A eta theta2 →
            0 < d ∧ d < theta1 ∧
              ∃ closed : SurgeryFlowCylinder F (F.slice t) t
                  ((F.parameters.h t)⁻¹ ^ 2) (Icc 0 d)
                  ((F.metric t).ball ((F.event t hEvent).caps i).tip
                    (A * F.parameters.h t)),
                ∃ initial : SurgeryCapInitialComparison F t hEvent i A,
                  SurgeryCapFamilyComparison F O.standard_flow A eta closed initial.chart ∧
                  (∀ hs z, z ∈ (F.metric t).ball ((F.event t hEvent).caps i).tip
                    (A * F.parameters.h t) → HEq (closed.forward 0 hs z) z) ∧
                  (∀ x ∈ U, E.forward a bottom x ∈
                    (F.metric t).ball ((F.event t hEvent).caps i).tip
                      (Rcap * F.parameters.h t)) ∧
                  (∀ x ∈ U, E.forward a bottom x ∈
                    (F.metric t).ball ((F.event t hEvent).caps i).tip
                      (A * F.parameters.h t)) ∧
                  ∀ htop hzero x, x ∈ U →
                    HEq (closed.forward d htop (E.forward a bottom x))
                      (E.forward 0 hzero x) := by
  obtain ⟨theta1, theta2, ht1, ht12, ht2, _hsigma, _hsigma1, hrate⟩ :=
    exists_cap_comparison_time_margin hc hT hK.le
  obtain ⟨Rcap, hRcap, hcapture⟩ := exists_source_bottom_cap_capture_radius g0 hD hK hc
  refine ⟨theta1, theta2, Rcap, ht1, ht12, ht2, hRcap, ?_⟩
  intro Rrequested
  obtain ⟨A, eta0, delta0, _hApos, hAmax, heta0, hetaHalf, hdelta0, hincluded⟩ :=
    exists_actualCap_included_comparison_cutoff P standard
      (by linarith only [ht1]) (ht12.trans ht2) (max Rcap Rrequested)
  have hRcapA : Rcap < A := (le_max_left _ _).trans_lt hAmax
  have hRA : Rrequested < A := (le_max_right _ _).trans_lt hAmax
  have hA := hRcap.trans hRcapA
  refine ⟨A, eta0, delta0, hRA, hRcapA, hA, heta0, hetaHalf, hdelta0, ?_⟩
  intro F hinitial O Oambient hmodel hpinch constants setup start rNext deltaBar
    hscales hdelta htime C U hU Q a ha E hscalar
  dsimp only
  intro hEvent hn i contact hcontact hcap hdistance hheight eta heta hetaSmall hbound hpersist
  let bottom : a ∈ Icc a 0 := ⟨le_rfl, ha.2.le⟩
  let t := O.H + a / Q
  let h := F.parameters.h t
  let d := (O.H - t) / h ^ 2
  let V := E.forward a bottom '' U
  let W := (F.metric t).ball ((F.event t hEvent).caps i).tip (A * h)
  have hQ := E.scale_pos
  have hh : 0 < h :=
    F.parameters.h_pos t (F.time_domain_nonnegative (F.surgery_times_subset hEvent))
  have htH : t < O.H := add_lt_of_neg_right _ (div_neg_of_neg_of_pos ha.2 hQ)
  have hAactual : F.standard_initial.cylindrical_end.radius + 5 < A := hinitial.symm ▸ hA
  have hfloor := insertedCap_scalarLower_of_persistence O hEvent i
    (by linarith only [ht1, ht12]) hAactual htH hbound hpersist
    (E.forward a bottom contact) hcap
  have hfixed (x : C.carrier) (hx : x ∈ U) :
      E.forward a bottom x ∈ (F.metric t).ball ((F.event t hEvent).caps i).tip (Rcap * h) :=
    hcapture F hinitial C ha.2 E hEvent i contact hcap hfloor
      (hscalar a bottom contact hcontact) hdistance x hx
  have hVcapture (x : C.carrier) (hx : x ∈ U) : E.forward a bottom x ∈ W := by
    have hfixed' := hfixed x hx
    change (F.metric t).edist _ _ < ENNReal.ofReal (Rcap * h) at hfixed'
    change (F.metric t).edist _ _ < ENNReal.ofReal (A * h)
    exact hfixed'.trans_le
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hRcapA.le hh.le))
  have hage := cap_stop_elapsed_lt_comparison_margin O E hU ha.2 hEvent i hAactual hK.le
    ht1 ht12 ht2 hrate (by linarith only [ha.1]) contact hcontact hcap
      (fun s hs => hscalar s hs contact hcontact) hbound hpersist
  have hdtheta : d < theta1 := by
    apply (div_lt_iff₀ (sq_pos_of_pos hh)).mpr
    apply (mul_lt_mul_iff_right₀ hQ).mp
    calc
      Q * (O.H - t) = -a := by dsimp only [t]; field_simp [hQ.ne']; ring
      _ < theta1 * (Q * h ^ 2) := hage
      _ = Q * (theta1 * h ^ 2) := by ring
  obtain ⟨hd, f, basedF, terminalF⟩ :=
    exists_cap_birth_cylinder_terminal_map E hU ha.2 h hh
  have hyV : E.forward a bottom contact ∈ V := mem_image_of_mem _ hcontact
  obtain ⟨e, initial, comparison, basedE⟩ :=
    Proofs.M47.capPersistence_persists_to_horizon O hEvent i hAactual V f basedF
      (E.forward a bottom contact) hyV hcap (hdtheta.trans ht12) hpersist
  have hclock : t + d / (h⁻¹ ^ 2) = O.H := by
    rw [surgeryCap_physical_time]
    dsimp only [d]
    rw [div_mul_cancel₀ _ (sq_pos_of_pos hh).ne']
    ring
  obtain ⟨closed, hclosed, basedClosed, _old, _contact⟩ := hincluded
    F hinitial O.standard_flow hmodel hpinch Oambient setup hscales hdelta t hEvent hn i d
      hd hdtheta.le W V e f initial eta heta hetaSmall comparison hheight
      (hclock.symm ▸ htime) basedE basedF (E.forward a bottom contact)
      (hVcapture contact hcontact) hyV
  refine ⟨hd, hdtheta, closed, initial, hclosed, basedClosed, hfixed, hVcapture, ?_⟩
  intro htop hzero x hx
  have heq : closed.forward d htop (E.forward a bottom x) =
      f.forward d htop (E.forward a bottom x) := by
    apply M44.cylinder_forward_eq_of_initial closed f hd.le Subset.rfl Subset.rfl
      (E.forward a bottom x) (hVcapture x hx) (mem_image_of_mem _ hx)
    exact eq_of_heq ((basedClosed _ _ (hVcapture x hx)).trans
      (basedF _ _ (mem_image_of_mem _ hx)).symm)
  exact (heq_of_eq heq).trans (terminalF htop hzero x hx)

end PoincareConjecture.M47
