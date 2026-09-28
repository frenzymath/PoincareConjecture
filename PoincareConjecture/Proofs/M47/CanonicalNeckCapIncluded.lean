import PoincareConjecture.Proofs.M47.CanonicalNeckCapAge
import PoincareConjecture.Proofs.M47.CanonicalNeckCapCapture
import PoincareConjecture.Proofs.M47.CanonicalNeckCapReclock
import PoincareConjecture.Proofs.M47.BlowupControlsCapIncluded
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_CapBirth










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

universe u

namespace PoincareConjecture.Proofs.M47



theorem exists_strongNeck_included_cap_comparison_capture_cutoff_above
    (P : M47Predecessors.{u}) {g0 : StandardInitialMetric}
    (standard : RepairedStandardCapExistenceData g0) {epsilon c : ℝ}
    (hepsilon : 0 < epsilon) (hsmall : epsilon ≤ 1 / 200) (hc : 0 < c) :
    ∃ theta1 theta2 : ℝ,
      1 / 2 < theta1 ∧ theta1 < theta2 ∧ theta2 < 1 ∧
      ∀ R : ℝ, ∃ A eta0 delta0 : ℝ, R < A ∧
      g0.cylindrical_end.radius + 5 < A ∧ 0 < eta0 ∧ eta0 ≤ 1 / 2 ∧ 0 < delta0 ∧
      ∀ (F : SurgeryFlowData.{u}), F.standard_initial = g0 →
      ∀ (O Oambient : SurgeryObservation F), HEq O.standard_flow standard.flow →
        SurgeryFlowPinched F →
      ∀ {constants : MetricSurgeryConstants} (setup : SurgeryControlSetup constants)
        {start rNext deltaBar : ℝ},
        SurgeryFixedScalesOn setup F Oambient start rNext deltaBar → deltaBar ≤ delta0 →
        O.H ∈ surgeryObservationInterval Oambient ∩ Ici start →
      ∀ (N : SurgeryStrongNeck F O.H epsilon)
        (U : TopologicalSpace.Opens (F.slice O.H).carrier),
        (U : Set (F.slice O.H).carrier) = N.neck.carrier →
      ∀ E : SurgeryFlowCylinder F (F.slice O.H) O.H 1
          (Icc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0) U,
        (∀ hs x, x ∈ U → HEq (E.forward 0 hs x) x) →
        (∀ s (hs : s ∈ Ioc (-1 : ℝ) 0)
          (hs' : s / (N.neck.scale⁻¹ ^ 2) ∈ Icc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0),
          ∀ x ∈ U,
            HEq (E.forward (s / (N.neck.scale⁻¹ ^ 2)) hs' x) (N.cylinder.forward s hs x)) →
        let a := -(N.neck.scale⁻¹ ^ 2)⁻¹
        let ha : a ∈ Icc a 0 :=
          ⟨le_rfl, neg_nonpos.mpr (inv_pos.mpr N.cylinder.scale_pos).le⟩
        let t := O.H + a / 1
        let d := (O.H - t) / (F.parameters.h t) ^ 2
        ∀ (hT : t ∈ F.surgery_times), ∀ [Nonempty (F.slice t).carrier],
        ∀ (i : Fin (F.event t hT).cap_count) (contact : U),
          E.forward a ha contact.val ∈ ((F.event t hT).caps i).carrier →
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
                (∀ x ∈ U, E.forward a ha x ∈
                  (F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t)) ∧
                ∀ htop x, x ∈ U → HEq (closed.forward d htop (E.forward a ha x)) x := by
  obtain ⟨theta1, theta2, ht1, ht12, ht2, hage⟩ := exists_strongNeck_cap_time_margin P hc
  obtain ⟨A0, hA0, hcapture⟩ :=
    exists_strongNeck_bottom_capture_radius P g0 hepsilon hsmall hc
  refine ⟨theta1, theta2, ht1, ht12, ht2, ?_⟩
  intro R
  let P44 : M44CapPersistencePredecessors.{u} := ⟨P.m04, P.m13.ordinary_flow⟩
  obtain ⟨A, eta0, delta0, _hApos, hAmax, heta0, hetaHalf, hdelta0, hincluded⟩ :=
    PoincareConjecture.M47.exists_actualCap_included_comparison_cutoff P44 standard
      (by linarith only [ht1]) (ht12.trans ht2) (max A0 R)
  have hAA0 : A0 < A := (le_max_left _ _).trans_lt hAmax
  have hRA : R < A := (le_max_right _ _).trans_lt hAmax
  have hA : g0.cylindrical_end.radius + 5 < A := hA0.trans hAA0
  refine ⟨A, eta0, delta0, hRA, hA,
    heta0, hetaHalf, hdelta0, ?_⟩
  intro F hinitial O Oambient hmodel hpinch constants setup start rNext deltaBar
    hscales hdelta htime N U hU E hbased hagree
  dsimp only
  intro hT hn i contact hcontact hheight eta heta hetaSmall hbound hpersist
  let Q := N.neck.scale⁻¹ ^ 2
  let a := -Q⁻¹
  have hQ : 0 < Q := N.cylinder.scale_pos
  have haNeg : a < (0 : ℝ) := neg_neg_of_pos (inv_pos.mpr hQ)
  have ha : a ∈ Icc a 0 := ⟨le_rfl, haNeg.le⟩
  let t := O.H + a / 1
  let h := F.parameters.h t
  let d := (O.H - t) / h ^ 2
  let V := E.forward a ha '' (U : Set (F.slice O.H).carrier)
  let W := (F.metric t).ball ((F.event t hT).caps i).tip (A * h)
  have hh : 0 < h :=
    F.parameters.h_pos t (F.time_domain_nonnegative (F.surgery_times_subset hT))
  have htH : t < O.H := by
    dsimp only [t]
    simpa only [div_one] using add_lt_of_neg_right O.H haNeg
  have hAactual : F.standard_initial.cylindrical_end.radius + 5 < A := hinitial.symm ▸ hA
  have hfloor := M46.insertedCap_scalarLower_of_persistence O hT i
    (by linarith only [ht1, ht12]) hAactual htH hbound hpersist
    (E.forward a ha contact.val) hcontact
  have hVcapture (x : (F.slice O.H).carrier) (hx : x ∈ U) : E.forward a ha x ∈ W := by
    have hcap := hcapture hinitial N U hU E hbased hagree hT i contact hcontact hfloor ⟨x, hx⟩
    change (F.metric t).edist ((F.event t hT).caps i).tip (E.forward a ha x) <
      ENNReal.ofReal (A0 * h) at hcap
    change (F.metric t).edist ((F.event t hT).caps i).tip (E.forward a ha x) <
      ENNReal.ofReal (A * h)
    exact hcap.trans_le (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hAA0.le hh.le))
  have hage' := (hage O N hsmall U hU E hbased hagree hT i contact hcontact
    A eta hAactual hbound hpersist).1
  have hlength : O.H - t = Q⁻¹ := by dsimp only [t, a]; ring
  have hdtheta : d < theta1 := by
    dsimp only [d]
    rw [hlength]
    exact (div_lt_iff₀ (sq_pos_of_pos hh)).mpr hage'
  obtain ⟨hd, f, basedF, terminalF⟩ :=
    exists_based_cap_birth_cylinder E U.isOpen haNeg h hh hbased
  have hyV : E.forward a ha contact.val ∈ V := mem_image_of_mem _ contact.property
  obtain ⟨e, initial, comparison, basedE⟩ := capPersistence_persists_to_horizon
    O hT i hAactual V f basedF (E.forward a ha contact.val) hyV hcontact
      (hdtheta.trans ht12) hpersist
  have hclock : t + d / (h⁻¹ ^ 2) = O.H := by
    rw [surgeryCap_physical_time]
    dsimp only [d]
    rw [div_mul_cancel₀ _ (sq_pos_of_pos hh).ne']
    ring
  obtain ⟨closed, hclosed, basedClosed, _old, _contact⟩ := hincluded
    F hinitial O.standard_flow hmodel hpinch Oambient setup hscales hdelta t hT hn i d
      hd hdtheta.le W V e f initial eta heta hetaSmall comparison hheight
      (hclock.symm ▸ htime) basedE basedF (E.forward a ha contact.val)
      (hVcapture contact.val contact.property) hyV
  refine ⟨hd, hdtheta, closed, initial, hclosed, basedClosed, hVcapture, ?_⟩
  intro htop x hx
  have hxW := hVcapture x hx
  have hxV : E.forward a ha x ∈ V := mem_image_of_mem _ hx
  have heq : closed.forward d htop (E.forward a ha x) =
      f.forward d htop (E.forward a ha x) := by
    apply M44.cylinder_forward_eq_of_initial closed f hd.le Subset.rfl Subset.rfl
      (E.forward a ha x) hxW hxV
    exact eq_of_heq ((basedClosed _ _ hxW).trans (basedF _ _ hxV).symm)
  exact (heq_of_eq heq).trans (terminalF htop x hx)



theorem exists_strongNeck_included_cap_comparison_capture_cutoff
    (P : M47Predecessors.{u}) {g0 : StandardInitialMetric}
    (standard : RepairedStandardCapExistenceData g0) {epsilon c : ℝ}
    (hepsilon : 0 < epsilon) (hsmall : epsilon ≤ 1 / 200) (hc : 0 < c) :
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
      ∀ (N : SurgeryStrongNeck F O.H epsilon)
        (U : TopologicalSpace.Opens (F.slice O.H).carrier),
        (U : Set (F.slice O.H).carrier) = N.neck.carrier →
      ∀ E : SurgeryFlowCylinder F (F.slice O.H) O.H 1
          (Icc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0) U,
        (∀ hs x, x ∈ U → HEq (E.forward 0 hs x) x) →
        (∀ s (hs : s ∈ Ioc (-1 : ℝ) 0)
          (hs' : s / (N.neck.scale⁻¹ ^ 2) ∈ Icc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0),
          ∀ x ∈ U,
            HEq (E.forward (s / (N.neck.scale⁻¹ ^ 2)) hs' x) (N.cylinder.forward s hs x)) →
        let a := -(N.neck.scale⁻¹ ^ 2)⁻¹
        let ha : a ∈ Icc a 0 :=
          ⟨le_rfl, neg_nonpos.mpr (inv_pos.mpr N.cylinder.scale_pos).le⟩
        let t := O.H + a / 1
        let d := (O.H - t) / (F.parameters.h t) ^ 2
        ∀ (hT : t ∈ F.surgery_times), ∀ [Nonempty (F.slice t).carrier],
        ∀ (i : Fin (F.event t hT).cap_count) (contact : U),
          E.forward a ha contact.val ∈ ((F.event t hT).caps i).carrier →
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
                (∀ x ∈ U, E.forward a ha x ∈
                  (F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t)) ∧
                ∀ htop x, x ∈ U → HEq (closed.forward d htop (E.forward a ha x)) x := by
  obtain ⟨theta1, theta2, ht1, ht12, ht2, radii⟩ :=
    exists_strongNeck_included_cap_comparison_capture_cutoff_above P standard
      hepsilon hsmall hc
  obtain ⟨A, eta0, delta0, _hApos, hA, heta0, hetaHalf, hdelta0, produce⟩ := radii 0
  exact ⟨theta1, theta2, A, eta0, delta0, ht1, ht12, ht2, hA,
    heta0, hetaHalf, hdelta0, produce⟩



theorem exists_strongNeck_included_cap_comparison_cutoff
    (P : M47Predecessors.{u}) {g0 : StandardInitialMetric}
    (standard : RepairedStandardCapExistenceData g0) {epsilon c : ℝ}
    (hepsilon : 0 < epsilon) (hsmall : epsilon ≤ 1 / 200) (hc : 0 < c) :
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
      ∀ (N : SurgeryStrongNeck F O.H epsilon)
        (U : TopologicalSpace.Opens (F.slice O.H).carrier),
        (U : Set (F.slice O.H).carrier) = N.neck.carrier →
      ∀ E : SurgeryFlowCylinder F (F.slice O.H) O.H 1
          (Icc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0) U,
        (∀ hs x, x ∈ U → HEq (E.forward 0 hs x) x) →
        (∀ s (hs : s ∈ Ioc (-1 : ℝ) 0)
          (hs' : s / (N.neck.scale⁻¹ ^ 2) ∈ Icc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0),
          ∀ x ∈ U,
            HEq (E.forward (s / (N.neck.scale⁻¹ ^ 2)) hs' x) (N.cylinder.forward s hs x)) →
        let a := -(N.neck.scale⁻¹ ^ 2)⁻¹
        let ha : a ∈ Icc a 0 :=
          ⟨le_rfl, neg_nonpos.mpr (inv_pos.mpr N.cylinder.scale_pos).le⟩
        let t := O.H + a / 1
        let d := (O.H - t) / (F.parameters.h t) ^ 2
        ∀ (hT : t ∈ F.surgery_times), ∀ [Nonempty (F.slice t).carrier],
        ∀ (i : Fin (F.event t hT).cap_count) (contact : U),
          E.forward a ha contact.val ∈ ((F.event t hT).caps i).carrier →
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
                ∀ htop x, x ∈ U → HEq (closed.forward d htop (E.forward a ha x)) x := by
  obtain ⟨theta1, theta2, A, eta0, delta0, ht1, ht12, ht2, hA,
    heta0, hetaHalf, hdelta0, produce⟩ :=
    exists_strongNeck_included_cap_comparison_capture_cutoff P standard hepsilon hsmall hc
  refine ⟨theta1, theta2, A, eta0, delta0, ht1, ht12, ht2, hA,
    heta0, hetaHalf, hdelta0, ?_⟩
  intro F hinitial O Oambient hmodel hpinch constants setup start rNext deltaBar
    hscales hdelta htime N U hU E hbased hagree
  dsimp only
  intro hT hn i contact hcontact hheight eta heta hetaSmall hbound hpersist
  obtain ⟨hd, hdt, closed, initial, comparison, based, _capture, terminal⟩ :=
    produce F hinitial O Oambient hmodel hpinch setup hscales hdelta htime
      N U hU E hbased hagree hT i contact hcontact hheight eta heta hetaSmall hbound hpersist
  exact ⟨hd, hdt, closed, initial, comparison, based, terminal⟩

end PoincareConjecture.Proofs.M47
