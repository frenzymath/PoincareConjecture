import PoincareConjecture.Proofs.M47.BlowupControlsSourceCapFactoryAbove

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

theorem exists_bounded_search_included_cap_cutoff_above
    (P : M46Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    {K Asearch : ℝ} (hK : 0 < K) (hAsearch : 0 ≤ Asearch) :
    ∃ theta1 theta2 Rcap : ℝ,
      1 / 2 < theta1 ∧ theta1 < theta2 ∧ theta2 < 1 ∧
      S.standard_initial.cylindrical_end.radius + 5 < Rcap ∧
      ∀ Rrequested : ℝ, ∃ A eta0 : ℝ, Rrequested < A ∧ Rcap < A ∧
      S.standard_initial.cylindrical_end.radius + 5 < A ∧ 0 < eta0 ∧ eta0 ≤ 1 / 2 ∧
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
          ∀ {base Q a : ℝ}, base ∈ Ico (surgeryEpochStart p.i) O.H → 128 ≤ Q →
            SurgeryCanonicalOn F (surgeryObservationInterval O ∩ Iio base) rNext →
          ∀ ha : a ∈ Ico (-1 : ℝ) 0, ∀ y : (F.slice base).carrier,
          ∀ E : SurgeryFlowCylinder F (F.slice base) base Q (Icc a 0)
              ((F.metric base).ball y (Asearch / Real.sqrt Q)),
            (∀ hs z, z ∈ (F.metric base).ball y (Asearch / Real.sqrt Q) →
              HEq (E.forward 0 hs z) z) →
            (∀ s hs z, z ∈ (F.metric base).ball y (Asearch / Real.sqrt Q) →
              (F.connection (base + s / Q)).scalarCurvature (E.forward s hs z) ≤ K * Q) →
            let bottom : a ∈ Icc a 0 := ⟨le_rfl, ha.2.le⟩
            let t := base + a / Q
            let d := (base - t) / (F.parameters.h t) ^ 2
            (∀ z ∈ (F.metric base).ball y (Asearch / Real.sqrt Q),
              ∀ v : TangentSpace (𝓡 3) z,
              (F.metric t).inner (E.forward a bottom z)
                  (mfderiv (𝓡 3) (𝓡 3) (E.forward a bottom) z v)
                  (mfderiv (𝓡 3) (𝓡 3) (E.forward a bottom) z v) ≤
                2 * (F.metric base).inner z v v) →
            ∀ (hT : t ∈ F.surgery_times), ∀ [Nonempty (F.slice t).carrier],
            ∀ (i : Fin (F.event t hT).cap_count) (contact : (F.slice base).carrier),
              contact ∈ (F.metric base).ball y (Asearch / Real.sqrt Q) →
              E.forward a bottom contact ∈ ((F.event t hT).caps i).carrier →
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
                    (∀ z ∈ (F.metric base).ball y (Asearch / Real.sqrt Q),
                      E.forward a bottom z ∈ (F.metric t).ball
                        ((F.event t hT).caps i).tip (Rcap * F.parameters.h t)) ∧
                    (∀ z ∈ (F.metric base).ball y (Asearch / Real.sqrt Q),
                      E.forward a bottom z ∈ (F.metric t).ball
                        ((F.event t hT).caps i).tip (A * F.parameters.h t)) ∧
                    ∀ htop z, z ∈ (F.metric base).ball y (Asearch / Real.sqrt Q) →
                      HEq (closed.forward d htop (E.forward a bottom z)) z := by
  obtain ⟨c, hc, scalarTolerance⟩ := exists_blowupCap_scalarRate_tolerance S.cap_persistence
  let P44 : M44CapPersistencePredecessors.{u} := ⟨P.m04, P.m13.ordinary_flow⟩
  obtain ⟨theta1, theta2, Rcap, ht1, ht12, ht2, hRcap, radii⟩ :=
    exists_search_enclosing_cap_comparison_cutoff P44 S.cap_persistence.standard_cap hAsearch hK hc
  refine ⟨theta1, theta2, Rcap, ht1, ht12, ht2, hRcap, fun Rrequested => ?_⟩
  obtain ⟨A, etaI, deltaI, hRA, hRcapA, hA, hetaI, hetaHalf, hdeltaI, included⟩ :=
    radii Rrequested
  have hApos : 0 < A := by linarith [S.standard_initial.cylindrical_end.radius_pos]
  obtain ⟨etaR, hetaR, _hetaRHalf, scalarBound⟩ := scalarTolerance A hApos theta2 ht2
  refine ⟨A, min etaI etaR, hRA, hRcapA, hA, lt_min hetaI hetaR,
    (min_le_left _ _).trans hetaHalf, ?_⟩
  intro eta heta hetaSmall rNext hrNext hrLast
  obtain ⟨deltaCap, hdeltaCap, hdeltaLast, capControl⟩ :=
    exists_first_failure_capCutoff S p hp rNext hrNext hrLast A eta theta2 hApos heta
      (by linarith only [ht1, ht12]) ht2
  let cutoff := min deltaCap (min deltaI (1 / 2))
  have hcutCap : cutoff ≤ deltaCap := min_le_left _ _
  have hcutI : cutoff ≤ deltaI := (min_le_right _ _).trans (min_le_left _ _)
  have hcutHalf : cutoff ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨cutoff, lt_min hdeltaCap (lt_min hdeltaI (by norm_num)),
    hcutCap.trans hdeltaLast, ?_⟩
  intro F O hH old hadmissible hpinch next overlap base Q a hBase h128 hearlier
    ha y E hbased hscalar
  dsimp only
  intro hmetric hT hn i contact hcontact hcap
  have hQ := E.scale_pos
  have hbasepos : 0 < base :=
    (show 0 < surgeryEpochStart p.i by unfold surgeryEpochStart; positivity).trans_le hBase.1
  have hinitial : F.standard_initial = S.standard_initial := by
    rw [old.standard_initial_eq, hp.setup_eq]
    exact S.setup_standard_initial_eq
  let raw := O.restrictTo base hbasepos hBase.2.le
  let oldRaw : SurgeryPrefixControls p F raw := old.restrictObservation hBase.2.le
  let short := raw.redecorateTo oldRaw.standard_initial_eq
  have hpflow : HEq p.setup.standard_flow S.cap_persistence.standard_cap.flow := by
    rw [hp.setup_eq]
    exact S.setup_standard_flow_eq
  have hmodel : HEq short.standard_flow S.cap_persistence.standard_cap.flow :=
    (Proofs.M46.redecorateTo_standard_flow raw oldRaw.standard_initial_eq).trans hpflow
  let t := base + a / Q
  have htBase : t < base := add_lt_of_neg_right _ (div_neg_of_neg_of_pos ha.2 hQ)
  have htWindow : t ∈ Ico (base - 1 / Q) base := by
    refine ⟨?_, htBase⟩
    have hdiv := div_le_div_of_nonneg_right ha.1 hQ.le
    simp only [neg_div] at hdiv
    dsimp only [t]
    linarith only [hdiv]
  have htOverlap := blowup_analytic_window_subset_overlap p hBase zero_le_one
    (by norm_num; exact h128) (le_refl Q) (by norm_num : (0 : ℝ) ≤ 1) htWindow
    (show t ∈ Icc (t - 0 / Q) t by simp)
  have caps := capControl F O hH old hadmissible hpinch (next.mono_delta hcutCap)
    (fun t ht' => (overlap t ht').trans hcutCap) base hbasepos hBase.2.le hearlier
  have htRaw : t ∈ surgeryObservationInterval raw := ⟨htOverlap.1.1, htBase⟩
  have hpersist : SurgeryCapPersistenceAlternative F short t hT i A eta theta2 :=
    caps t hT htRaw htOverlap.2.1 i
  have scales := old.capPersistenceScales hH hrLast next overlap
  have hdeltaBirth : F.parameters.delta t ≤ 1 / 2 :=
    (scales.delta_le t ⟨htOverlap.1, htOverlap.2.1⟩).trans hcutHalf
  have hdeltaSq : (F.parameters.delta t) ^ 2 ≤ 1 := by
    have hdOne : F.parameters.delta t ≤ 1 := by linarith only [hdeltaBirth]
    simpa only [one_pow] using
      pow_le_pow_left₀ (F.parameters.delta_pos t htOverlap.1.1).le hdOne 2
  have hh : 0 < F.parameters.h t := F.parameters.h_pos t htOverlap.1.1
  have hheight : (F.parameters.h t) ^ 2 ≤ 1 := by
    have hrOne : F.parameters.r t ≤ 1 :=
      (F.parameters.r_le_epsilon t htOverlap.1.1).trans
        (by linarith [F.parameters.epsilon_le])
    have hhOne : F.parameters.h t ≤ 1 := calc
      _ ≤ F.parameters.delta t ^ 2 * F.parameters.r t := F.parameters.h_le t htOverlap.1.1
      _ ≤ 1 * F.parameters.r t :=
        mul_le_mul_of_nonneg_right hdeltaSq (F.parameters.r_pos t htOverlap.1.1).le
      _ = F.parameters.r t := one_mul _
      _ ≤ 1 := hrOne
    simpa only [one_pow] using pow_le_pow_left₀ hh.le hhOne 2
  have hendpoint : short.H ∈ surgeryObservationInterval O ∩
      Ici (surgeryEpochStart (p.i - 1)) :=
    ⟨⟨hbasepos.le, hBase.2⟩, htOverlap.2.1.trans htBase.le⟩
  let _inst : Nonempty (F.slice (short.H + a / Q)).carrier := hn
  apply included F hinitial short O hmodel hpinch p.setup scales hcutI hendpoint
    ha y E hbased hscalar hmetric hT i contact hcontact hcap hheight eta heta
    (hetaSmall.trans (min_le_left _ _)) ?_ hpersist
  intro J V f initial comparison s hs hst z hz
  exact scalarBound F hinitial short hmodel t hT hn i J V f initial
    (Proofs.M47.capFamilyComparison_mono_tolerance heta
      (hetaSmall.trans (min_le_right _ _)) comparison) hh s hs hst z hz

end PoincareConjecture.M47
