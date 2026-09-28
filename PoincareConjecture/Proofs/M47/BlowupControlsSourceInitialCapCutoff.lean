import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialCapAnchor
import PoincareConjecture.Proofs.M47.BlowupControlsCapCutoff
import PoincareConjecture.Proofs.M47.BlowupControlsWindow
import PoincareConjecture.Proofs.M47.CanonicalCapComparisonTolerance
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialSearchClock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

theorem exists_source_initial_search_cap_duration
    {A m rate theta : ℝ} (hA : 0 < A) (hm : 0 < m)
    (hrate : 0 < rate) (htheta : 0 < theta) :
    ∃ L d : ℝ, 1 ≤ L ∧ 2 / m ≤ L ∧ 0 < d ∧ d ≤ m ∧ d ≤ 1 ∧
      64 * A * L * (2 * d) ≤ 1 ∧ 16 * L * d ≤ rate * theta := by
  obtain ⟨L, d0, hL, hmL, hd0, hd0m, hd0One, hshort⟩ :=
    exists_source_initial_search_duration hA hm
  let d := min d0 (rate * theta / (16 * L))
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hd : 0 < d := lt_min hd0 (div_pos (mul_pos hrate htheta) (by positivity))
  have hdd0 : d ≤ d0 := min_le_left _ _
  refine ⟨L, d, hL, hmL, hd, hdd0.trans hd0m, hdd0.trans hd0One, ?_, ?_⟩
  · calc
      _ ≤ 64 * A * L * (2 * d0) :=
        mul_le_mul_of_nonneg_left (by linarith only [hdd0]) (by positivity)
      _ ≤ 1 := hshort
  · have h := (le_div_iff₀ (show 0 < 16 * L by positivity)).mp
      (min_le_right d0 (rate * theta / (16 * L)))
    change d * (16 * L) ≤ rate * theta at h
    nlinarith only [h]

theorem exists_source_initial_cap_anchor_cutoff
    (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p) :
    ∃ rate : ℝ, 0 < rate ∧ ∀ theta : ℝ, 0 < theta → theta < 1 →
      ∀ A : ℝ, S.standard_initial.cylindrical_end.radius + 5 < A →
      ∃ eta0 : ℝ, 0 < eta0 ∧ eta0 ≤ 1 / 2 ∧
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
          ∀ {C : GeneralizedSliceCarrier.{u}} {V : Set C.carrier}
            {base Q shift T b c d L : ℝ},
            base ∈ Ico (surgeryEpochStart p.i) O.H → 0 ≤ T → 64 * (T + 1) ≤ Q →
            SurgeryCanonicalOn F (surgeryObservationInterval O ∩ Iio base) rNext →
            shift ≤ 0 → -T ≤ shift + b →
          ∀ E : SurgeryFlowCylinder F C (base + shift / Q) Q (Icc b 0) V,
            IsOpen V → ∀ hc : c < 0, ∀ hb : b ∈ Icc (c - d) c,
            0 < L → 16 * L * d ≤ rate * theta →
          ∀ (hT : (base + shift / Q) + b / Q ∈ F.surgery_times)
            [Nonempty (F.slice ((base + shift / Q) + b / Q)).carrier]
            (i : Fin (F.event ((base + shift / Q) + b / Q) hT).cap_count)
            (x : C.carrier), x ∈ V →
            E.forward b ⟨le_rfl, hb.2.trans hc.le⟩ x ∈
              ((F.event ((base + shift / Q) + b / Q) hT).caps i).carrier →
            (F.connection ((base + shift / Q) + b / Q)).scalarCurvature
              (E.forward b ⟨le_rfl, hb.2.trans hc.le⟩ x) ≤ 4 * L * Q →
          let origin := base + shift / Q
          let birth := origin + b / Q
          let h := F.parameters.h birth
          let sigma := (c - b) / (Q * h ^ 2)
          rate / (8 * L) ≤ Q * h ^ 2 ∧
            ∃ e : SurgeryFlowCylinder F (F.slice birth) birth (h⁻¹ ^ 2)
                (Ico 0 (surgeryCapDuration birth origin h theta))
                ((F.metric birth).ball ((F.event birth hT).caps i).tip (A * h)),
              ∃ initial : SurgeryCapInitialComparison F birth hT i A,
                SurgeryCapFamilyComparison F (O.redecorateTo old.standard_initial_eq).standard_flow
                  A eta e initial.chart ∧
                (∀ hs y, y ∈ (F.metric birth).ball ((F.event birth hT).caps i).tip
                  (A * h) → HEq (e.forward 0 hs y) y) ∧
                ∃ hAnchor : sigma ∈ Ico 0 (surgeryCapDuration birth origin h theta),
                  sigma ≤ theta / 2 ∧
                  (⟨birth + sigma / (h⁻¹ ^ 2),
                    e.forward sigma hAnchor (E.forward b ⟨le_rfl, hb.2.trans hc.le⟩ x)⟩ :
                      Σ t, (F.slice t).carrier) =
                    ⟨origin + c / Q, E.forward c ⟨hb.2, hc.le⟩ x⟩ := by
  obtain ⟨rate, hrate, tolerance⟩ := exists_blowupCap_scalarRate_tolerance S.cap_persistence
  refine ⟨rate, hrate, ?_⟩
  intro theta htheta hthetaOne A hA
  have hApos : 0 < A := by linarith [S.standard_initial.cylindrical_end.radius_pos]
  obtain ⟨eta0, heta0, hetaHalf, scalarBound⟩ := tolerance A hApos theta hthetaOne
  refine ⟨eta0, heta0, hetaHalf, ?_⟩
  intro eta heta hetaSmall rNext hrNext hrLast
  obtain ⟨cutoff, hcutoff, hcutoffLast, capControl⟩ :=
    exists_first_failure_capCutoff S p hp rNext hrNext hrLast A eta theta hApos heta
      htheta hthetaOne
  refine ⟨cutoff, hcutoff, hcutoffLast, ?_⟩
  intro F O hH old hadmissible hpinched next overlap C V base Q shift T b c d L
    hBase hTwindow hScale hearlier hShift hWindow E hV hc hb hL hDuration hEvent hn i x hx
    hcap hscalar
  let origin := base + shift / Q
  let birth := origin + b / Q
  have hQ := E.scale_pos
  have hbNeg : b < 0 := hb.2.trans_lt hc
  have hbirthOrigin : birth < origin :=
    add_lt_of_neg_right _ (div_neg_of_neg_of_pos hbNeg hQ)
  have horiginBase : origin ≤ base := by
    dsimp only [origin]
    exact add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hShift hQ.le)
  have hbirthBase : birth < base := hbirthOrigin.trans_le horiginBase
  have hbirthWindow : birth ∈ Ico (base - T / Q) base := by
    refine ⟨?_, hbirthBase⟩
    have h := div_le_div_of_nonneg_right hWindow hQ.le
    dsimp only [birth, origin]
    rw [add_div, neg_div] at h
    linarith only [h]
  have hOverlap := blowup_analytic_window_subset_overlap p hBase hTwindow hScale
    (le_refl Q) (by norm_num : (0 : ℝ) ≤ 1) hbirthWindow
    (show birth ∈ Icc (birth - 0 / Q) birth by simp)
  have horiginPos : 0 < origin := hOverlap.1.1.trans_lt hbirthOrigin
  have horiginH : origin ≤ O.H := horiginBase.trans hBase.2.le
  let raw := O.restrictTo origin horiginPos horiginH
  let oldRaw : SurgeryPrefixControls p F raw := old.restrictObservation horiginH
  let short := raw.redecorateTo oldRaw.standard_initial_eq
  have hcanonical : SurgeryCanonicalOn F (surgeryObservationInterval O ∩ Iio origin) rNext :=
    hearlier.restrict (fun _ ht => ⟨ht.1, ht.2.trans_le horiginBase⟩)
  have caps := capControl F O hH old hadmissible hpinched next overlap
    origin horiginPos horiginH hcanonical
  have hRaw : birth ∈ surgeryObservationInterval raw := ⟨hOverlap.1.1, hbirthOrigin⟩
  have hpersist : SurgeryCapPersistenceAlternative F short birth hEvent i A eta theta :=
    caps birth hEvent hRaw hOverlap.2.1 i
  have hinitial : F.standard_initial = S.standard_initial := by
    rw [old.standard_initial_eq, hp.setup_eq, S.setup_standard_initial_eq]
  have hpflow : HEq p.setup.standard_flow S.cap_persistence.standard_cap.flow := by
    rw [hp.setup_eq]
    exact S.setup_standard_flow_eq
  have hmodel : HEq short.standard_flow S.cap_persistence.standard_cap.flow :=
    (Proofs.M46.redecorateTo_standard_flow raw oldRaw.standard_initial_eq).trans hpflow
  have hh : 0 < F.parameters.h birth := F.parameters.h_pos birth hOverlap.1.1
  have hAactual : F.standard_initial.cylindrical_end.radius + 5 < A :=
    hinitial.symm ▸ hA
  let _inst : Nonempty (F.slice (short.H + b / Q)).carrier := hn
  apply source_initial_cap_anchor_comparison short E hV hc hb hL htheta hDuration
    hEvent i hAactual x hx hcap hscalar ?_ hpersist
  intro J U f initial comparison s hs hst z hz
  exact scalarBound F hinitial short hmodel birth hEvent hn i J U f initial
    (Proofs.M47.capFamilyComparison_mono_tolerance heta hetaSmall comparison) hh s hs hst z hz

end PoincareConjecture.M47
