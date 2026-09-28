import PoincareConjecture.Proofs.M47.BlowupControlsSourceCapture
import PoincareConjecture.Proofs.M47.BlowupControlsCapIncluded
import PoincareConjecture.Proofs.M47.BlowupControlsCapStop
import PoincareConjecture.Proofs.M47.BlowupControlsCapScalar
import PoincareConjecture.Proofs.M47.CanonicalNeckCapReclock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M47

open Proofs.M46

theorem exists_search_included_cap_comparison_cutoff
    (P : M44CapPersistencePredecessors.{u}) {g0 : StandardInitialMetric}
    (standard : RepairedStandardCapExistenceData g0)
    {Asearch K c : ℝ} (hAsearch : 0 ≤ Asearch) (hK : 0 < K) (hc : 0 < c) :
    ∃ theta1 theta2 A eta0 delta0 : ℝ,
      1 / 2 < theta1 ∧ theta1 < theta2 ∧ theta2 < 1 ∧
      g0.cylindrical_end.radius + 5 < A ∧ 0 < eta0 ∧ eta0 ≤ 1 / 2 ∧ 0 < delta0 ∧
      ∀ (F : SurgeryFlowData.{u}), F.standard_initial = g0 →
      ∀ (O Oambient : SurgeryObservation F), HEq O.standard_flow standard.flow →
        SurgeryFlowPinched F →
      ∀ {constants : MetricSurgeryConstants} (setup : SurgeryControlSetup constants)
        {start rNext deltaBar : ℝ},
        SurgeryFixedScalesOn setup F Oambient start rNext deltaBar → deltaBar ≤ delta0 →
        O.H ∈ surgeryObservationInterval Oambient ∩ Ici start →
      ∀ {Q a : ℝ} (ha : a ∈ Ico (-1 : ℝ) 0) (p : (F.slice O.H).carrier),
      ∀ E : SurgeryFlowCylinder F (F.slice O.H) O.H Q (Icc a 0)
          ((F.metric O.H).ball p (Asearch / Real.sqrt Q)),
        (∀ hs x, x ∈ (F.metric O.H).ball p (Asearch / Real.sqrt Q) →
          HEq (E.forward 0 hs x) x) →
        (∀ s (hs : s ∈ Icc a 0), ∀ x ∈ (F.metric O.H).ball p (Asearch / Real.sqrt Q),
          (F.connection (O.H + s / Q)).scalarCurvature (E.forward s hs x) ≤ K * Q) →
        let bottom : a ∈ Icc a 0 := ⟨le_rfl, ha.2.le⟩
        let t := O.H + a / Q
        let d := (O.H - t) / (F.parameters.h t) ^ 2
        (∀ x ∈ (F.metric O.H).ball p (Asearch / Real.sqrt Q),
          ∀ v : TangentSpace (𝓡 3) x,
          (F.metric t).inner (E.forward a bottom x)
              (mfderiv (𝓡 3) (𝓡 3) (E.forward a bottom) x v)
              (mfderiv (𝓡 3) (𝓡 3) (E.forward a bottom) x v) ≤
            2 * (F.metric O.H).inner x v v) →
        ∀ (hT : t ∈ F.surgery_times), ∀ [Nonempty (F.slice t).carrier],
        ∀ (i : Fin (F.event t hT).cap_count) (contact : (F.slice O.H).carrier),
          contact ∈ (F.metric O.H).ball p (Asearch / Real.sqrt Q) →
          E.forward a bottom contact ∈ ((F.event t hT).caps i).carrier →
          (F.parameters.h t) ^ 2 ≤ 1 →
        ∀ eta : ℝ, 0 < eta → eta ≤ eta0 →
          (∀ (J : Set ℝ) (V : Set (F.slice t).carrier)
            (f : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J V)
            (initial : SurgeryCapInitialComparison F t hT i A),
            SurgeryCapFamilyComparison F O.standard_flow A eta f initial.chart →
            ∀ (s : ℝ) (hs : s ∈ J), s ≤ theta2 →
            ∀ z ∈ F.standard_initial.metric.ball 0 A,
              c / (2 * (1 - s) * (F.parameters.h t) ^ 2) ≤
                (F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2))).scalarCurvature
                  (f.forward s hs (initial.chart z))) →
          SurgeryCapPersistenceAlternative F O t hT i A eta theta2 →
          0 < d ∧ d < theta1 ∧
            ∃ closed : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2)
                (Icc 0 d)
                ((F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t)),
              ∃ initial : SurgeryCapInitialComparison F t hT i A,
                SurgeryCapFamilyComparison F O.standard_flow A eta closed initial.chart ∧
                (∀ hs z, z ∈ (F.metric t).ball ((F.event t hT).caps i).tip
                  (A * F.parameters.h t) → HEq (closed.forward 0 hs z) z) ∧
                (∀ x ∈ (F.metric O.H).ball p (Asearch / Real.sqrt Q),
                  E.forward a bottom x ∈ (F.metric t).ball
                    ((F.event t hT).caps i).tip (A * F.parameters.h t)) ∧
                ∀ htop x, x ∈ (F.metric O.H).ball p (Asearch / Real.sqrt Q) →
                  HEq (closed.forward d htop (E.forward a bottom x)) x := by
  obtain ⟨theta1, theta2, ht1, ht12, ht2, _hsigma, _hsigma1, hrate⟩ :=
    exists_cap_comparison_time_margin hc zero_le_one hK.le
  obtain ⟨A0, hA0, hcapture⟩ := exists_search_bottom_cap_capture_radius g0 hAsearch hK hc
  obtain ⟨A, eta0, delta0, _hApos, hAA0, heta0, hetaHalf, hdelta0, hincluded⟩ :=
    exists_actualCap_included_comparison_cutoff P standard
      (by linarith only [ht1]) (ht12.trans ht2) A0
  have hA := hA0.trans hAA0
  refine ⟨theta1, theta2, A, eta0, delta0, ht1, ht12, ht2, hA,
    heta0, hetaHalf, hdelta0, ?_⟩
  intro F hinitial O Oambient hmodel hpinch constants setup start rNext deltaBar
    hscales hdelta htime Q a ha p E hbased hscalar
  dsimp only
  intro hmetric hT hn i contact hcontact hcap hheight eta heta hetaSmall hbound hpersist
  let U := (F.metric O.H).ball p (Asearch / Real.sqrt Q)
  have hU : IsOpen U := M04.initial_ball_isOpen _ _ _
  let bottom : a ∈ Icc a 0 := ⟨le_rfl, ha.2.le⟩
  let t := O.H + a / Q
  let h := F.parameters.h t
  let d := (O.H - t) / h ^ 2
  let V := E.forward a bottom '' U
  let W := (F.metric t).ball ((F.event t hT).caps i).tip (A * h)
  have hQ := E.scale_pos
  have hh : 0 < h :=
    F.parameters.h_pos t (F.time_domain_nonnegative (F.surgery_times_subset hT))
  have htH : t < O.H := by
    dsimp only [t]
    exact add_lt_of_neg_right _ (div_neg_of_neg_of_pos ha.2 hQ)
  have hAactual : F.standard_initial.cylindrical_end.radius + 5 < A := hinitial.symm ▸ hA
  have hfloor := insertedCap_scalarLower_of_persistence O hT i
    (by linarith only [ht1, ht12]) hAactual htH hbound hpersist
    (E.forward a bottom contact) hcap
  have hVcapture (x : (F.slice O.H).carrier) (hx : x ∈ U) : E.forward a bottom x ∈ W := by
    have hcap' := hcapture F hinitial ha.2 p E hT i contact hcontact hcap hfloor
      (hscalar a bottom contact hcontact) hmetric x hx
    change (F.metric t).edist ((F.event t hT).caps i).tip (E.forward a bottom x) <
      ENNReal.ofReal (A0 * h) at hcap'
    change (F.metric t).edist ((F.event t hT).caps i).tip (E.forward a bottom x) <
      ENNReal.ofReal (A * h)
    exact hcap'.trans_le (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hAA0.le hh.le))
  have hage := cap_stop_elapsed_lt_comparison_margin O E hU ha.2 hT i hAactual hK.le
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
    Proofs.M47.exists_based_cap_birth_cylinder E hU ha.2 h hh hbased
  have hyV : E.forward a bottom contact ∈ V := mem_image_of_mem _ hcontact
  obtain ⟨e, initial, comparison, basedE⟩ := Proofs.M47.capPersistence_persists_to_horizon
    O hT i hAactual V f basedF (E.forward a bottom contact) hyV hcap
      (hdtheta.trans ht12) hpersist
  have hclock : t + d / (h⁻¹ ^ 2) = O.H := by
    rw [surgeryCap_physical_time]
    dsimp only [d]
    rw [div_mul_cancel₀ _ (sq_pos_of_pos hh).ne']
    ring
  obtain ⟨closed, hclosed, basedClosed, _old, _contact⟩ := hincluded
    F hinitial O.standard_flow hmodel hpinch Oambient setup hscales hdelta t hT hn i d
      hd hdtheta.le W V e f initial eta heta hetaSmall comparison hheight
      (hclock.symm ▸ htime) basedE basedF (E.forward a bottom contact)
      (hVcapture contact hcontact) hyV
  refine ⟨hd, hdtheta, closed, initial, hclosed, basedClosed, hVcapture, ?_⟩
  intro htop x hx
  have heq : closed.forward d htop (E.forward a bottom x) =
      f.forward d htop (E.forward a bottom x) := by
    apply M44.cylinder_forward_eq_of_initial closed f hd.le Subset.rfl Subset.rfl
      (E.forward a bottom x) (hVcapture x hx) (mem_image_of_mem _ hx)
    exact eq_of_heq ((basedClosed _ _ (hVcapture x hx)).trans
      (basedF _ _ (mem_image_of_mem _ hx)).symm)
  exact (heq_of_eq heq).trans (terminalF htop x hx)

end PoincareConjecture.M47
