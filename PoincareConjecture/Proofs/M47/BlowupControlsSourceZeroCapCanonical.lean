import PoincareConjecture.Proofs.M47.BlowupControlsSourceCompactCanonical
import PoincareConjecture.Proofs.M47.BlowupControlsSourceBirthFactory











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47



theorem exists_first_failure_zero_cap_canonical_cutoff
    (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    {Asearch : ℝ} (hAsearch : 0 < Asearch)
    (pointwise : ∀ theta : ℝ, theta < 1 → ∀ v ∈ Icc 0 theta,
      ∀ z : StandardCapSpace,
      ∃ A0 eta0 nearTime Q0 : ℝ, ∃ V : Set StandardCapSpace,
        0 < A0 ∧ 0 < eta0 ∧ 0 < nearTime ∧ 0 < Q0 ∧ IsOpen V ∧ z ∈ V ∧
        ∀ A : ℝ, A0 ≤ A → ∀ eta : ℝ, 0 < eta → eta ≤ eta0 →
        ∀ rNext : ℝ, 0 < rNext → rNext ≤ p.r (Fin.last p.i) →
          ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
          ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
            O.H ≤ surgeryEpochStart (p.i + 1) →
          ∀ prior : SurgeryPrefixControls p F O,
            SurgeryFlowAdmissible F → SurgeryFlowPinched F →
            SurgeryPostPrefixScales p F O rNext cutoff →
            (∀ b ∈ surgeryObservationInterval O ∩ overlapInterval p,
              F.parameters.delta b ≤ cutoff) →
          ∀ (t : ℝ) (hT : t ∈ F.surgery_times),
          ∀ [Nonempty (F.slice t).carrier], ∀ (i : Fin (F.event t hT).cap_count)
            (J : Set ℝ)
            (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J
              ((F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t)))
            (initial : SurgeryCapInitialComparison F t hT i A),
            SurgeryCapFamilyComparison F
              (O.redecorateTo prior.standard_initial_eq).standard_flow A eta e initial.chart →
          ∀ hzero : (0 : ℝ) ∈ J,
            (∀ y ∈ (F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t),
              HEq (e.forward 0 hzero y) y) →
            0 < F.parameters.h t →
          ∀ (s : ℝ) (hs : s ∈ J), s ∈ Icc 0 theta → Icc 0 s ⊆ J →
            |s - v| < nearTime → ∀ z' ∈ V,
            let base := t + s / ((F.parameters.h t)⁻¹ ^ 2)
            let x := e.forward s hs (initial.chart z')
            let Q := (F.connection base).scalarCurvature x
            base ∈ Ico (surgeryEpochStart p.i) O.H → Q0 ≤ Q → rNext⁻¹ ^ 2 ≤ Q →
            SurgeryCanonicalOn F (surgeryObservationInterval O ∩ Iio base) rNext →
            Q * (base - t) ∈ Icc 0 1 →
            SurgeryCanonicalControl F base x S.setup.epsilon S.setup.C) :
    ∃ Q0 : ℝ, 0 < Q0 ∧
      ∀ rNext : ℝ, 0 < rNext → rNext ≤ p.r (Fin.last p.i) →
        ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
        ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
          O.H ≤ surgeryEpochStart (p.i + 1) →
        ∀ _prior : SurgeryPrefixControls p F O,
          SurgeryFlowAdmissible F → SurgeryFlowPinched F →
          SurgeryPostPrefixScales p F O rNext cutoff →
          (∀ b ∈ surgeryObservationInterval O ∩ overlapInterval p,
            F.parameters.delta b ≤ cutoff) →
        ∀ (W : M33RegularHistoryWindow F) (H : M33RegularHistoryData W)
          {base Q : ℝ} (ht : base ∈ H.generalized.interval),
          base ∈ Ico (surgeryEpochStart p.i) O.H → Q0 ≤ Q → rNext⁻¹ ^ 2 ≤ Q →
          SurgeryCanonicalOn F (surgeryObservationInterval O ∩ Iio base) rNext →
        ∀ x : (H.generalized.slice base).carrier,
          H.generalized.scalar ⟨base, x⟩ = Q →
        ∀ hT : base ∈ F.surgery_times, ∀ [Nonempty (F.slice base).carrier],
        ∀ (i : Fin (F.event base hT).cap_count) (contact : (F.slice base).carrier),
          contact ∈ (F.metric base).ball (H.history.forward base ht x) (Asearch / Real.sqrt Q) →
          contact ∈ ((F.event base hT).caps i).carrier →
          SurgeryCanonicalControl F base (H.history.forward base ht x)
            F.parameters.epsilon F.parameters.C := by
  obtain ⟨Qbirth, R, hQbirth, hR, factory⟩ :=
    exists_zero_age_search_cap_comparison_cutoff S hAsearch
  have hRpos : 0 < R := by linarith [S.standard_initial.cylindrical_end.radius_pos]
  obtain ⟨Ac, etaC, Qc, _hAc, hRAc, hetaC, hetaCSmall, _hQc, compact⟩ :=
    exists_compact_source_standard_canonical_transfer S p (by positivity : 0 < 2 * R)
      (pointwise 0 (by norm_num))
  obtain ⟨deltaBirth, hdeltaBirth, birth⟩ :=
    factory Ac (by linarith only [hRpos, hRAc]) etaC hetaC hetaCSmall
  refine ⟨max Qbirth Qc, hQbirth.trans_le (le_max_left _ _), ?_⟩
  intro rNext hrNext hrLast
  obtain ⟨deltaC, hdeltaC, hdeltaCLast, transfer⟩ :=
    compact Ac le_rfl etaC hetaC le_rfl rNext hrNext hrLast
  refine ⟨min deltaBirth deltaC, lt_min hdeltaBirth hdeltaC,
    (min_le_right _ _).trans hdeltaCLast, ?_⟩
  intro F O hH prior hadmissible hpinch next overlap W H base Q ht hBase hLarge
    hScale hEarlier x hscale hT hn i contact hcontact hcap
  have hbase : 0 < base :=
    (show 0 < surgeryEpochStart p.i by unfold surgeryEpochStart; positivity).trans_le hBase.1
  have hQ : 0 < Q := hQbirth.trans_le ((le_max_left _ _).trans hLarge)
  have hinitial : F.standard_initial = S.standard_initial := by
    rw [prior.standard_initial_eq, hp.setup_eq]
    exact S.setup_standard_initial_eq
  have heps : F.parameters.epsilon = S.setup.epsilon := by rw [prior.epsilon_eq, hp.setup_eq]
  have hC : F.parameters.C = S.setup.C := by rw [prior.C_eq, hp.setup_eq]
  have hpflow : HEq p.setup.standard_flow S.cap_persistence.standard_cap.flow := by
    rw [hp.setup_eq]
    exact S.setup_standard_flow_eq
  have hmodel := (Proofs.M46.redecorateTo_standard_flow O prior.standard_initial_eq).trans hpflow
  have hpast : SurgeryCanonicalOn F (Ico 0 base) rNext := by
    intro b hb
    exact hEarlier b ⟨⟨hb.1, hb.2.trans hBase.2⟩, hb.2⟩
  have hdelta : F.parameters.delta base ≤ deltaBirth :=
    (next.delta_le base ⟨⟨hbase.le, hBase.2⟩, hBase.1⟩).trans (min_le_left _ _)
  obtain ⟨j, e, initial, comparison, based, _capture, z, hz, hzy, hzRadius⟩ :=
    birth F hinitial prior.local_constants_eq heps hC
      (O.redecorateTo prior.standard_initial_eq).standard_flow hmodel W H ht hbase hQ
      hpinch hpast hScale x hscale ((le_max_left _ _).trans hLarge) hT hdelta
      i contact hcontact hcap
  have hzR : S.standard_initial.metric.edist 0 z ≤ ENNReal.ofReal (2 * R) := by
    simpa only [hinitial] using hzRadius
  have hzSource : initial.chart z ∈ (F.metric base).ball ((F.event base hT).caps j).tip
      (Ac * F.parameters.h base) :=
    comparison.choose_spec.2.2.2.1 ▸ mem_image_of_mem initial.chart hz
  have hh : 0 < F.parameters.h base := F.parameters.h_pos base hbase.le
  have hzero : (0 : ℝ) ∈ Icc 0 0 := ⟨le_rfl, le_rfl⟩
  let y := H.history.forward base ht x
  have hpoint : (⟨base + 0 / ((F.parameters.h base)⁻¹ ^ 2),
      e.forward 0 hzero (initial.chart z)⟩ : Σ s, (F.slice s).carrier) =
        ⟨base, y⟩ := by
    apply Sigma.ext (by simp)
    exact (based hzero (initial.chart z) hzSource).trans (heq_of_eq hzy)
  let GuardedControl (w : Σ s, (F.slice s).carrier) : Prop :=
    w.1 ∈ Ico (surgeryEpochStart p.i) O.H →
    Qc ≤ (F.connection w.1).scalarCurvature w.2 →
    rNext⁻¹ ^ 2 ≤ (F.connection w.1).scalarCurvature w.2 →
    SurgeryCanonicalOn F (surgeryObservationInterval O ∩ Iio w.1) rNext →
    (F.connection w.1).scalarCurvature w.2 * (w.1 - base) ∈ Icc 0 1 →
    SurgeryCanonicalControl F w.1 w.2 S.setup.epsilon S.setup.C
  have hcontrol : GuardedControl ⟨base + 0 / ((F.parameters.h base)⁻¹ ^ 2),
      e.forward 0 hzero (initial.chart z)⟩ :=
    transfer F O hH prior hadmissible hpinch (next.mono_delta (min_le_right _ _))
      (fun b hb => (overlap b hb).trans (min_le_right _ _)) base hT j (Icc 0 0)
      e initial comparison hzero (based hzero) hh 0 hzero hzero (Subset.refl _) z hzR
  have hbaseControl : GuardedControl ⟨base, y⟩ := (congrArg GuardedControl hpoint).mp hcontrol
  have hscalar : (F.connection base).scalarCurvature y = Q :=
    (H.scalar_pullback base ht x).trans hscale
  have hCanonical : SurgeryCanonicalControl F base y S.setup.epsilon S.setup.C := by
    apply hbaseControl hBase
    · simpa only [hscalar] using (le_max_right Qbirth Qc).trans hLarge
    · simpa only [hscalar] using hScale
    · exact hEarlier
    · simp
  simpa only [heps, hC] using hCanonical

end PoincareConjecture.M47
