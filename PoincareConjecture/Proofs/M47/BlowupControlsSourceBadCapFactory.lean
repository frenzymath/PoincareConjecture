import PoincareConjecture.Proofs.M47.BlowupControlsSourceCapFactoryAbove
import PoincareConjecture.Proofs.M47.BlowupControlsSourceTipExclusion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

theorem exists_first_failure_search_bad_cap_cutoff_above
    (P : M46Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    {Asearch : ℝ} (hAsearch : 0 < Asearch) :
    ∃ Q0 tau theta1 theta2 Rcap : ℝ,
      0 < Q0 ∧ 0 < tau ∧ tau ≤ 1 ∧
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
          ∀ (W : M33RegularHistoryWindow F) (H : M33RegularHistoryData W)
            {base Q a : ℝ} (ht : base ∈ H.generalized.interval),
            base ∈ Ico (surgeryEpochStart p.i) O.H → Q0 ≤ Q → rNext⁻¹ ^ 2 ≤ Q →
            SurgeryCanonicalOn F (surgeryObservationInterval O ∩ Iio base) rNext →
            ∀ ha : a ∈ Ico (-tau) 0, ∀ x : (H.generalized.slice base).carrier,
            H.generalized.scalar ⟨base, x⟩ = Q →
            ¬ SurgeryCanonicalControl F base (H.history.forward base ht x)
              F.parameters.epsilon F.parameters.C →
          ∀ E : SurgeryFlowCylinder F (F.slice base) base Q (Icc a 0)
              ((F.metric base).ball (H.history.forward base ht x) (Asearch / Real.sqrt Q)),
            (∀ hs y,
              y ∈ (F.metric base).ball (H.history.forward base ht x) (Asearch / Real.sqrt Q) →
                HEq (E.forward 0 hs y) y) →
            let bottom : a ∈ Icc a 0 := ⟨le_rfl, ha.2.le⟩
            let t := base + a / Q
            let d := (base - t) / (F.parameters.h t) ^ 2
            ∀ (hT : t ∈ F.surgery_times), ∀ [Nonempty (F.slice t).carrier],
            ∀ (i : Fin (F.event t hT).cap_count) (contact : (F.slice base).carrier),
              contact ∈ (F.metric base).ball (H.history.forward base ht x) (Asearch / Real.sqrt Q) →
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
                    (∀ y ∈ (F.metric base).ball (H.history.forward base ht x)
                        (Asearch / Real.sqrt Q),
                      E.forward a bottom y ∈ (F.metric t).ball
                        ((F.event t hT).caps i).tip (Rcap * F.parameters.h t)) ∧
                    (∀ y ∈ (F.metric base).ball (H.history.forward base ht x)
                        (Asearch / Real.sqrt Q),
                      E.forward a bottom y ∈ (F.metric t).ball
                        ((F.event t hT).caps i).tip (A * F.parameters.h t)) ∧
                    (∀ htop y,
                      y ∈ (F.metric base).ball (H.history.forward base ht x)
                        (Asearch / Real.sqrt Q) →
                        HEq (closed.forward d htop (E.forward a bottom y)) y) ∧
                    ∃ z ∈ F.standard_initial.metric.ball 0 A,
                      initial.chart z = E.forward a bottom (H.history.forward base ht x) ∧
                      (57 / 10 : ℝ) * S.setup.epsilon⁻¹ <
                        ((S.cap_persistence.standard_cap.flow.metric d).edist 0 z).toReal *
                          Real.sqrt
                            ((S.cap_persistence.standard_cap.flow.connection d).scalarCurvature
                              z) := by
  obtain ⟨Q0, tau, theta1, theta2, Rcap, hQ0, htau, htauOne, ht1, ht12, ht2,
    hRcap, radii⟩ :=
    exists_first_failure_search_included_cap_cutoff_above P S B p hp hAsearch.le
  obtain ⟨A0, _hA0, tolerances⟩ := exists_source_bad_point_tip_exclusion_tolerance S
    (by linarith only [ht1] : 0 < theta1) (ht12.trans ht2)
  refine ⟨Q0, tau, theta1, theta2, Rcap, hQ0, htau, htauOne, ht1, ht12, ht2,
    hRcap, fun Rrequested => ?_⟩
  obtain ⟨A, etaFactory, hRequested, hRcapA, hA, hetaFactory, hetaHalf, factory⟩ :=
    radii (max A0 Rrequested)
  have hA0A : A0 ≤ A := ((le_max_left _ _).trans_lt hRequested).le
  obtain ⟨etaTip, hetaTip, outside⟩ := tolerances A hA0A
  refine ⟨A, min etaFactory etaTip, (le_max_right _ _).trans_lt hRequested,
    hRcapA, hA, lt_min hetaFactory hetaTip, (min_le_left _ _).trans hetaHalf, ?_⟩
  intro eta heta hetaSmall rNext hrNext hrLast
  obtain ⟨cutoff, hcutoff, hcutLast, included⟩ :=
    factory eta heta (hetaSmall.trans (min_le_left _ _)) rNext hrNext hrLast
  refine ⟨cutoff, hcutoff, hcutLast, ?_⟩
  intro F O hH old hadmissible hpinch next overlap W H base Q a ht hBase hLarge
    hThreshold hearlier ha x hscale hfail E hbased
  dsimp only
  intro hT hn i contact hcontact hcap
  obtain ⟨hd, hdtheta, closed, initial, comparison, based, capture, image, top⟩ :=
    included F O hH old hadmissible hpinch next overlap W H ht hBase hLarge
      hThreshold hearlier ha x hscale E hbased hT i contact hcontact hcap
  refine ⟨hd, hdtheta, closed, initial, comparison, based, capture, image, top, ?_⟩
  have hinitial : F.standard_initial = S.standard_initial := by
    rw [old.standard_initial_eq, hp.setup_eq]
    exact S.setup_standard_initial_eq
  have heps : F.parameters.epsilon = S.setup.epsilon := by rw [old.epsilon_eq, hp.setup_eq]
  have hC : F.parameters.C = S.setup.C := by rw [old.C_eq, hp.setup_eq]
  have hpflow : HEq p.setup.standard_flow S.cap_persistence.standard_cap.flow := by
    rw [hp.setup_eq]
    exact S.setup_standard_flow_eq
  have hmodel : HEq (O.redecorateTo old.standard_initial_eq).standard_flow
      S.cap_persistence.standard_cap.flow :=
    (Proofs.M46.redecorateTo_standard_flow O old.standard_initial_eq).trans hpflow
  have hcenter : H.history.forward base ht x ∈
      (F.metric base).ball (H.history.forward base ht x) (Asearch / Real.sqrt Q) := by
    change (F.metric base).edist _ _ < ENNReal.ofReal (Asearch / Real.sqrt Q)
    rw [M36.metric_edist_self]
    exact ENNReal.ofReal_pos.mpr (div_pos hAsearch (Real.sqrt_pos.mpr E.scale_pos))
  exact outside F hinitial heps hC _ hmodel base (base + a / Q) hT hn i closed initial
    eta heta (hetaSmall.trans (min_le_right _ _)) comparison ⟨hd.le, hdtheta.le⟩
    _ (H.history.forward base ht x) (image _ hcenter) (fun hs => top hs _ hcenter) hfail

end PoincareConjecture.M47
