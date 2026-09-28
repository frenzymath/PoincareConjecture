import PoincareConjecture.Proofs.M47.CanonicalNeckCapIncluded
import PoincareConjecture.Proofs.M47.CanonicalCapComparisonTolerance
import PoincareConjecture.Proofs.M47.BlowupControlsCapScalar
import PoincareConjecture.Proofs.M47.BlowupControlsCapCutoff
import PoincareConjecture.Proofs.M47.FirstFailureWindow
import PoincareConjecture.Proofs.M47.CanonicalNeckOrdinaryBridge










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

universe u

namespace PoincareConjecture.Proofs.M47



theorem exists_firstFailure_included_cap_comparison_capture_cutoff_above
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p) :
    ∃ theta1 theta2 : ℝ,
      1 / 2 < theta1 ∧ theta1 < theta2 ∧ theta2 < 1 ∧
      ∀ R : ℝ, ∃ A eta0 : ℝ, R < A ∧
      S.standard_initial.cylindrical_end.radius + 5 < A ∧
      0 < eta0 ∧ eta0 ≤ 1 / 2 ∧
      ∀ eta : ℝ, 0 < eta → eta ≤ eta0 →
      ∀ rNext : ℝ, 0 < rNext → rNext ≤ p.r (Fin.last p.i) →
        ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
          ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
            O.H ≤ surgeryEpochStart (p.i + 1) →
          ∀ old : SurgeryPrefixControls p F O,
            SurgeryFlowAdmissible F → SurgeryFlowPinched F →
            SurgeryPostPrefixScales p F O rNext cutoff →
            (∀ t ∈ surgeryObservationInterval O ∩ overlapInterval p,
              F.parameters.delta t ≤ cutoff) →
          ∀ T : ℝ, T ∈ Ico (surgeryEpochStart p.i) O.H →
            SurgeryCanonicalOn F (Ico 0 T) rNext →
          ∀ (N : SurgeryStrongNeck F T F.parameters.epsilon),
            rNext⁻¹ ^ 2 ≤ (F.connection T).scalarCurvature N.neck.center →
          ∀ (U : TopologicalSpace.Opens (F.slice T).carrier),
            (U : Set (F.slice T).carrier) = N.neck.carrier →
          ∀ E : SurgeryFlowCylinder F (F.slice T) T 1
              (Icc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0) U,
            (∀ hs x, x ∈ U → HEq (E.forward 0 hs x) x) →
            (∀ s (hs : s ∈ Ioc (-1 : ℝ) 0)
              (hs' : s / (N.neck.scale⁻¹ ^ 2) ∈ Icc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0),
              ∀ x ∈ U,
                HEq (E.forward (s / (N.neck.scale⁻¹ ^ 2)) hs' x)
                  (N.cylinder.forward s hs x)) →
            let a := -(N.neck.scale⁻¹ ^ 2)⁻¹
            let ha : a ∈ Icc a 0 :=
              ⟨le_rfl, neg_nonpos.mpr (inv_pos.mpr N.cylinder.scale_pos).le⟩
            let t := T + a / 1
            let d := (T - t) / (F.parameters.h t) ^ 2
            ∀ (hT : t ∈ F.surgery_times), ∀ [Nonempty (F.slice t).carrier],
            ∀ (i : Fin (F.event t hT).cap_count) (contact : U),
              E.forward a ha contact.val ∈ ((F.event t hT).caps i).carrier →
              0 < d ∧ d < theta1 ∧
                ∃ closed : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2)
                    (Icc 0 d)
                    ((F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t)),
                  ∃ initial : SurgeryCapInitialComparison F t hT i A,
                    SurgeryCapFamilyComparison F
                      (O.redecorateTo old.standard_initial_eq).standard_flow
                      A eta closed initial.chart ∧
                    (∀ hs z, z ∈ (F.metric t).ball ((F.event t hT).caps i).tip
                      (A * F.parameters.h t) → HEq (closed.forward 0 hs z) z) ∧
                    (∀ x ∈ U, E.forward a ha x ∈ (F.metric t).ball
                      ((F.event t hT).caps i).tip (A * F.parameters.h t)) ∧
                    ∀ htop x, x ∈ U →
                      HEq (closed.forward d htop (E.forward a ha x)) x := by
  obtain ⟨c, hc, scalarTolerance⟩ :=
    PoincareConjecture.M47.exists_blowupCap_scalarRate_tolerance S.cap_persistence
  have hsmall : p.setup.epsilon ≤ 1 / 200 :=
    p.setup.epsilon_le.trans (min_le_left _ _)
  obtain ⟨theta1, theta2, ht1, ht12, ht2, radii⟩ :=
    exists_strongNeck_included_cap_comparison_capture_cutoff_above
      P S.cap_persistence.standard_cap
      p.setup.epsilon_pos hsmall hc
  refine ⟨theta1, theta2, ht1, ht12, ht2, ?_⟩
  intro R
  obtain ⟨A, etaI, deltaI, hRA, hA, hetaI, hetaHalf, hdeltaI, included⟩ := radii R
  have hApos : 0 < A := by linarith [S.standard_initial.cylindrical_end.radius_pos]
  obtain ⟨etaR, hetaR, _hetaRHalf, scalarBound⟩ := scalarTolerance A hApos theta2 ht2
  let eta0 := min etaI etaR
  refine ⟨A, eta0, hRA, hA,
    lt_min hetaI hetaR, (min_le_left _ _).trans hetaHalf, ?_⟩
  intro eta heta hetaSmall rNext hrNext hrLast
  have hetaI' : eta ≤ etaI := hetaSmall.trans (min_le_left _ _)
  have hetaR' : eta ≤ etaR := hetaSmall.trans (min_le_right _ _)
  obtain ⟨deltaCap, hdeltaCap, hdeltaLast, capControl⟩ :=
    PoincareConjecture.M47.exists_first_failure_capCutoff S p hp rNext hrNext hrLast
      A eta theta2 hApos heta (by linarith only [ht1, ht12]) ht2
  let cutoff := min deltaCap (min deltaI (1 / 2))
  have hcutoff : 0 < cutoff := lt_min hdeltaCap (lt_min hdeltaI (by norm_num))
  have hcutCap : cutoff ≤ deltaCap := min_le_left _ _
  have hcutI : cutoff ≤ deltaI := (min_le_right _ _).trans (min_le_left _ _)
  have hcutHalf : cutoff ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨cutoff, hcutoff, hcutCap.trans hdeltaLast, ?_⟩
  intro F O hH old hadmissible hpinch next overlap T hT hcanonical N hhigh U hU
    E hbased hagree
  dsimp only
  intro hSurgery hn i contact hcontact
  have hTpos : 0 < T :=
    (show 0 < surgeryEpochStart p.i by unfold surgeryEpochStart; positivity).trans_le hT.1
  let raw := O.restrictTo T hTpos hT.2.le
  let oldRaw : SurgeryPrefixControls p F raw := old.restrictObservation hT.2.le
  let short := raw.redecorateTo oldRaw.standard_initial_eq
  have hinitial : F.standard_initial = S.standard_initial := by
    rw [old.standard_initial_eq, hp.setup_eq, S.setup_standard_initial_eq]
  have hpflow : HEq p.setup.standard_flow S.cap_persistence.standard_cap.flow := by
    rw [hp.setup_eq]
    exact S.setup_standard_flow_eq
  have hmodel : HEq short.standard_flow S.cap_persistence.standard_cap.flow :=
    (M46.redecorateTo_standard_flow raw oldRaw.standard_initial_eq).trans hpflow
  have hpast : SurgeryCanonicalOn F (surgeryObservationInterval O ∩ Iio T) rNext := by
    intro t ht
    exact hcanonical t ⟨ht.1.1, ht.2⟩
  have caps := capControl F O hH old hadmissible hpinch (next.mono_delta hcutCap)
    (fun t ht => (overlap t ht).trans hcutCap) T hTpos hT.2.le hpast
  let Q := N.neck.scale⁻¹ ^ 2
  let a := -Q⁻¹
  let t := T + a / 1
  have hQ : 0 < Q := N.cylinder.scale_pos
  have hQeq : Q = (F.connection T).scalarCurvature N.neck.center := by
    rw [← N.connection_eq]
    exact neck_scale_inverse_square N.neck
  have hbottom : surgeryEpochStart (p.i - 1) < t := by
    have hb := firstFailure_neck_bottom_after_overlap p hrNext hrLast hT.1
      (show rNext⁻¹ ^ 2 ≤ Q by rw [hQeq]; exact hhigh)
    simpa only [t, a, div_one, sub_eq_add_neg] using hb
  have hstart0 : 0 < surgeryEpochStart (p.i - 1) := by
    unfold surgeryEpochStart
    positivity
  have htT : t < T := by
    dsimp only [t, a]
    simp only [div_one]
    linarith only [inv_pos.mpr hQ]
  have htRaw : t ∈ surgeryObservationInterval raw :=
    ⟨(hstart0.trans hbottom).le, htT⟩
  have htAmbient : t ∈ surgeryObservationInterval O :=
    ⟨htRaw.1, htT.trans hT.2⟩
  have hpersist : SurgeryCapPersistenceAlternative F short t hSurgery i A eta theta2 :=
    caps t hSurgery htRaw hbottom.le i
  have scales := old.capPersistenceScales hH hrLast next overlap
  have hdeltaBirth : F.parameters.delta t ≤ 1 / 2 :=
    (scales.delta_le t ⟨htAmbient, hbottom.le⟩).trans hcutHalf
  have hdeltaSq : (F.parameters.delta t) ^ 2 ≤ 1 := by
    have hd1 : F.parameters.delta t ≤ 1 := by linarith only [hdeltaBirth]
    simpa only [one_pow] using
      pow_le_pow_left₀ (F.parameters.delta_pos t htAmbient.1).le hd1 2
  have hh : 0 < F.parameters.h t := F.parameters.h_pos t htAmbient.1
  have hheight : (F.parameters.h t) ^ 2 ≤ 1 := by
    have hepsilonOne : F.parameters.epsilon ≤ 1 := by linarith [F.parameters.epsilon_le]
    have hrOne : F.parameters.r t ≤ 1 :=
      (F.parameters.r_le_epsilon t htAmbient.1).trans hepsilonOne
    have hle : F.parameters.h t ≤ 1 := calc
      _ ≤ F.parameters.delta t ^ 2 * F.parameters.r t := F.parameters.h_le t htAmbient.1
      _ ≤ 1 * F.parameters.r t :=
        mul_le_mul_of_nonneg_right hdeltaSq (F.parameters.r_pos t htAmbient.1).le
      _ = F.parameters.r t := one_mul _
      _ ≤ 1 := hrOne
    simpa only [one_pow] using pow_le_pow_left₀ hh.le hle 2
  let N0 : SurgeryStrongNeck F short.H p.setup.epsilon := {
    neck := N.neck
    epsilon_eq := N.epsilon_eq.trans old.epsilon_eq
    connection_eq := N.connection_eq
    cylinder := N.cylinder
    terminal_identity := N.terminal_identity
    metric_comparison := by simpa only [old.epsilon_eq] using N.metric_comparison }
  have hendpoint : short.H ∈ surgeryObservationInterval O ∩
      Ici (surgeryEpochStart (p.i - 1)) :=
    ⟨⟨hTpos.le, hT.2⟩, hbottom.le.trans htT.le⟩
  let : Nonempty (F.slice (short.H + -(N0.neck.scale⁻¹ ^ 2)⁻¹ / 1)).carrier := hn
  apply included F hinitial short O hmodel hpinch p.setup scales hcutI hendpoint
    N0 U hU E hbased hagree hSurgery i contact hcontact hheight eta heta hetaI'
      ?_ hpersist
  intro J V f initial comparison s hs hst z hz
  exact scalarBound F hinitial short hmodel t hSurgery hn i J V f initial
    (capFamilyComparison_mono_tolerance heta hetaR' comparison) hh s hs hst z hz



theorem exists_firstFailure_included_cap_comparison_capture_cutoff
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p) :
    ∃ theta1 theta2 A eta0 : ℝ,
      1 / 2 < theta1 ∧ theta1 < theta2 ∧ theta2 < 1 ∧
      S.standard_initial.cylindrical_end.radius + 5 < A ∧
      0 < eta0 ∧ eta0 ≤ 1 / 2 ∧
      ∀ eta : ℝ, 0 < eta → eta ≤ eta0 →
      ∀ rNext : ℝ, 0 < rNext → rNext ≤ p.r (Fin.last p.i) →
        ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
          ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
            O.H ≤ surgeryEpochStart (p.i + 1) →
          ∀ old : SurgeryPrefixControls p F O,
            SurgeryFlowAdmissible F → SurgeryFlowPinched F →
            SurgeryPostPrefixScales p F O rNext cutoff →
            (∀ t ∈ surgeryObservationInterval O ∩ overlapInterval p,
              F.parameters.delta t ≤ cutoff) →
          ∀ T : ℝ, T ∈ Ico (surgeryEpochStart p.i) O.H →
            SurgeryCanonicalOn F (Ico 0 T) rNext →
          ∀ (N : SurgeryStrongNeck F T F.parameters.epsilon),
            rNext⁻¹ ^ 2 ≤ (F.connection T).scalarCurvature N.neck.center →
          ∀ (U : TopologicalSpace.Opens (F.slice T).carrier),
            (U : Set (F.slice T).carrier) = N.neck.carrier →
          ∀ E : SurgeryFlowCylinder F (F.slice T) T 1
              (Icc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0) U,
            (∀ hs x, x ∈ U → HEq (E.forward 0 hs x) x) →
            (∀ s (hs : s ∈ Ioc (-1 : ℝ) 0)
              (hs' : s / (N.neck.scale⁻¹ ^ 2) ∈ Icc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0),
              ∀ x ∈ U,
                HEq (E.forward (s / (N.neck.scale⁻¹ ^ 2)) hs' x)
                  (N.cylinder.forward s hs x)) →
            let a := -(N.neck.scale⁻¹ ^ 2)⁻¹
            let ha : a ∈ Icc a 0 :=
              ⟨le_rfl, neg_nonpos.mpr (inv_pos.mpr N.cylinder.scale_pos).le⟩
            let t := T + a / 1
            let d := (T - t) / (F.parameters.h t) ^ 2
            ∀ (hT : t ∈ F.surgery_times), ∀ [Nonempty (F.slice t).carrier],
            ∀ (i : Fin (F.event t hT).cap_count) (contact : U),
              E.forward a ha contact.val ∈ ((F.event t hT).caps i).carrier →
              0 < d ∧ d < theta1 ∧
                ∃ closed : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2)
                    (Icc 0 d)
                    ((F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t)),
                  ∃ initial : SurgeryCapInitialComparison F t hT i A,
                    SurgeryCapFamilyComparison F
                      (O.redecorateTo old.standard_initial_eq).standard_flow
                      A eta closed initial.chart ∧
                    (∀ hs z, z ∈ (F.metric t).ball ((F.event t hT).caps i).tip
                      (A * F.parameters.h t) → HEq (closed.forward 0 hs z) z) ∧
                    (∀ x ∈ U, E.forward a ha x ∈ (F.metric t).ball
                      ((F.event t hT).caps i).tip (A * F.parameters.h t)) ∧
                    ∀ htop x, x ∈ U →
                      HEq (closed.forward d htop (E.forward a ha x)) x := by
  obtain ⟨theta1, theta2, ht1, ht12, ht2, radii⟩ :=
    exists_firstFailure_included_cap_comparison_capture_cutoff_above P S p hp
  obtain ⟨A, eta0, _hApos, hA, heta0, hetaHalf, produce⟩ := radii 0
  exact ⟨theta1, theta2, A, eta0, ht1, ht12, ht2, hA, heta0, hetaHalf, produce⟩



theorem exists_firstFailure_included_cap_comparison_cutoff
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p) :
    ∃ theta1 theta2 A eta0 : ℝ,
      1 / 2 < theta1 ∧ theta1 < theta2 ∧ theta2 < 1 ∧
      S.standard_initial.cylindrical_end.radius + 5 < A ∧
      0 < eta0 ∧ eta0 ≤ 1 / 2 ∧
      ∀ eta : ℝ, 0 < eta → eta ≤ eta0 →
      ∀ rNext : ℝ, 0 < rNext → rNext ≤ p.r (Fin.last p.i) →
        ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
          ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
            O.H ≤ surgeryEpochStart (p.i + 1) →
          ∀ old : SurgeryPrefixControls p F O,
            SurgeryFlowAdmissible F → SurgeryFlowPinched F →
            SurgeryPostPrefixScales p F O rNext cutoff →
            (∀ t ∈ surgeryObservationInterval O ∩ overlapInterval p,
              F.parameters.delta t ≤ cutoff) →
          ∀ T : ℝ, T ∈ Ico (surgeryEpochStart p.i) O.H →
            SurgeryCanonicalOn F (Ico 0 T) rNext →
          ∀ (N : SurgeryStrongNeck F T F.parameters.epsilon),
            rNext⁻¹ ^ 2 ≤ (F.connection T).scalarCurvature N.neck.center →
          ∀ (U : TopologicalSpace.Opens (F.slice T).carrier),
            (U : Set (F.slice T).carrier) = N.neck.carrier →
          ∀ E : SurgeryFlowCylinder F (F.slice T) T 1
              (Icc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0) U,
            (∀ hs x, x ∈ U → HEq (E.forward 0 hs x) x) →
            (∀ s (hs : s ∈ Ioc (-1 : ℝ) 0)
              (hs' : s / (N.neck.scale⁻¹ ^ 2) ∈ Icc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0),
              ∀ x ∈ U,
                HEq (E.forward (s / (N.neck.scale⁻¹ ^ 2)) hs' x)
                  (N.cylinder.forward s hs x)) →
            let a := -(N.neck.scale⁻¹ ^ 2)⁻¹
            let ha : a ∈ Icc a 0 :=
              ⟨le_rfl, neg_nonpos.mpr (inv_pos.mpr N.cylinder.scale_pos).le⟩
            let t := T + a / 1
            let d := (T - t) / (F.parameters.h t) ^ 2
            ∀ (hT : t ∈ F.surgery_times), ∀ [Nonempty (F.slice t).carrier],
            ∀ (i : Fin (F.event t hT).cap_count) (contact : U),
              E.forward a ha contact.val ∈ ((F.event t hT).caps i).carrier →
              0 < d ∧ d < theta1 ∧
                ∃ closed : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2)
                    (Icc 0 d)
                    ((F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t)),
                  ∃ initial : SurgeryCapInitialComparison F t hT i A,
                    SurgeryCapFamilyComparison F
                      (O.redecorateTo old.standard_initial_eq).standard_flow
                      A eta closed initial.chart ∧
                    (∀ hs z, z ∈ (F.metric t).ball ((F.event t hT).caps i).tip
                      (A * F.parameters.h t) → HEq (closed.forward 0 hs z) z) ∧
                    ∀ htop x, x ∈ U →
                      HEq (closed.forward d htop (E.forward a ha x)) x := by
  obtain ⟨theta1, theta2, A, eta0, ht1, ht12, ht2, hA, heta0, hetaHalf, produce⟩ :=
    exists_firstFailure_included_cap_comparison_capture_cutoff P S p hp
  refine ⟨theta1, theta2, A, eta0, ht1, ht12, ht2, hA, heta0, hetaHalf, ?_⟩
  intro eta heta hetaSmall rNext hrNext hrLast
  obtain ⟨cutoff, hcutoff, hlast, produce⟩ := produce eta heta hetaSmall rNext hrNext hrLast
  refine ⟨cutoff, hcutoff, hlast, ?_⟩
  intro F O hH old admissible pinched scales overlap T hT past N hhigh U hU
    E hbased hagree
  dsimp only
  intro hSurgery hn i contact hcontact
  obtain ⟨hd, hdt, closed, initial, comparison, based, _capture, terminal⟩ :=
    produce F O hH old admissible pinched scales overlap T hT past N hhigh
      U hU E hbased hagree hSurgery i contact hcontact
  exact ⟨hd, hdt, closed, initial, comparison, based, terminal⟩

end PoincareConjecture.Proofs.M47
