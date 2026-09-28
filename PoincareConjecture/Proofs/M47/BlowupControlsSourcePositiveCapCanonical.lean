import PoincareConjecture.Proofs.M47.BlowupControlsSourceCompactCanonical
import PoincareConjecture.Proofs.M47.BlowupControlsSourceCapFactoryAbove
import PoincareConjecture.Proofs.M47.BlowupControlsSourceBirthCenter

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

theorem exists_first_failure_positive_cap_canonical_cutoff
    (P : M46Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
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
    ∃ Q0 tau : ℝ, 0 < Q0 ∧ 0 < tau ∧ tau ≤ 1 ∧
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
          {base Q a : ℝ} (ht : base ∈ H.generalized.interval),
          base ∈ Ico (surgeryEpochStart p.i) O.H → Q0 ≤ Q → rNext⁻¹ ^ 2 ≤ Q →
          SurgeryCanonicalOn F (surgeryObservationInterval O ∩ Iio base) rNext →
        ∀ ha : a ∈ Ico (-tau) 0, ∀ x : (H.generalized.slice base).carrier,
          H.generalized.scalar ⟨base, x⟩ = Q →
        ∀ E : SurgeryFlowCylinder F (F.slice base) base Q (Icc a 0)
            ((F.metric base).ball (H.history.forward base ht x) (Asearch / Real.sqrt Q)),
          (∀ hs y,
            y ∈ (F.metric base).ball (H.history.forward base ht x) (Asearch / Real.sqrt Q) →
              HEq (E.forward 0 hs y) y) →
          let bottom : a ∈ Icc a 0 := ⟨le_rfl, ha.2.le⟩
          let t := base + a / Q
          ∀ (hT : t ∈ F.surgery_times), ∀ [Nonempty (F.slice t).carrier],
          ∀ (i : Fin (F.event t hT).cap_count) (contact : (F.slice base).carrier),
            contact ∈ (F.metric base).ball (H.history.forward base ht x) (Asearch / Real.sqrt Q) →
            E.forward a bottom contact ∈ ((F.event t hT).caps i).carrier →
            SurgeryCanonicalControl F base (H.history.forward base ht x)
              F.parameters.epsilon F.parameters.C := by
  obtain ⟨Qfactory, tau, theta1, theta2, Rcap, hQfactory, htau, htauOne,
    htheta1, htheta12, htheta2, hRcap, radii⟩ :=
    exists_first_failure_search_included_cap_cutoff_above P S B p hp hAsearch.le
  have hR : 0 < Rcap := by linarith [S.standard_initial.cylindrical_end.radius_pos]
  obtain ⟨Ac, etaC, Qc, _hAc, _hRAc, hetaC, hetaCSmall, hQc, compact⟩ :=
    exists_compact_source_standard_canonical_transfer S p (by positivity : 0 < 2 * Rcap)
      (pointwise theta1 (htheta12.trans htheta2))
  obtain ⟨A, etaI, hAcA, hRA, _hA, hetaI, _hetaIHalf, factory⟩ := radii Ac
  let eta := min etaI etaC
  have heta : 0 < eta := lt_min hetaI hetaC
  have hetaSmall : eta ≤ 1 / 1000 := (min_le_right _ _).trans hetaCSmall
  refine ⟨max Qfactory Qc, tau, hQfactory.trans_le (le_max_left _ _),
    htau, htauOne, ?_⟩
  intro rNext hrNext hrLast
  obtain ⟨deltaI, hdeltaI, hdeltaILast, included⟩ :=
    factory eta heta (min_le_left _ _) rNext hrNext hrLast
  obtain ⟨deltaC, hdeltaC, _hdeltaCLast, transfer⟩ :=
    compact A hAcA.le eta heta (min_le_right _ _) rNext hrNext hrLast
  refine ⟨min deltaI deltaC, lt_min hdeltaI hdeltaC,
    (min_le_left _ _).trans hdeltaILast, ?_⟩
  intro F O hH prior hadmissible hpinch next overlap W H base Q a ht hBase hLarge
    hScale hEarlier ha x hscale E hbased
  dsimp only
  intro hT hn i contact hcontact hcap
  obtain ⟨hd, hdTheta, closed, initial, comparison, closedBased, captured,
    _included, top⟩ := included F O hH prior hadmissible hpinch
      (next.mono_delta (min_le_left _ _))
      (fun b hb => (overlap b hb).trans (min_le_left _ _)) W H ht hBase
      ((le_max_left _ _).trans hLarge) hScale hEarlier ha x hscale E hbased
      hT i contact hcontact hcap
  let t := base + a / Q
  let d := (base - t) / (F.parameters.h t) ^ 2
  let y := H.history.forward base ht x
  have hQ : 0 < Q := E.scale_pos
  have hy : y ∈ (F.metric base).ball y (Asearch / Real.sqrt Q) := by
    change (F.metric base).edist y y < ENNReal.ofReal (Asearch / Real.sqrt Q)
    rw [M36.metric_edist_self]
    exact ENNReal.ofReal_pos.mpr (div_pos hAsearch (Real.sqrt_pos.mpr hQ))
  have hzero : (0 : ℝ) ∈ Icc 0 d := ⟨le_rfl, hd.le⟩
  have htop : d ∈ Icc 0 d := ⟨hd.le, le_rfl⟩
  obtain ⟨z, _hz, hzy, hzRadius⟩ := exists_cap_birth_center_in_fixed_ball
    hR hRA.le heta hetaSmall closed initial comparison hzero
      (closedBased hzero) (captured y hy)
  have hinitial : F.standard_initial = S.standard_initial := by
    rw [prior.standard_initial_eq, hp.setup_eq]
    exact S.setup_standard_initial_eq
  have hzR : S.standard_initial.metric.edist 0 z ≤ ENNReal.ofReal (2 * Rcap) := by
    simpa only [hinitial] using hzRadius
  have hh : 0 < F.parameters.h t :=
    F.parameters.h_pos t (F.time_domain_nonnegative (F.surgery_times_subset hT))
  have hclock : t + d / ((F.parameters.h t)⁻¹ ^ 2) = base := by
    rw [surgeryCap_physical_time]
    dsimp only [d]
    rw [div_mul_cancel₀ _ (sq_pos_of_pos hh).ne']
    ring
  have hpoint : (⟨t + d / ((F.parameters.h t)⁻¹ ^ 2),
      closed.forward d htop (initial.chart z)⟩ : Σ s, (F.slice s).carrier) =
        ⟨base, y⟩ := by
    apply Sigma.ext hclock
    rw [hzy]
    exact top htop y hy
  let GuardedControl (w : Σ s, (F.slice s).carrier) : Prop :=
    w.1 ∈ Ico (surgeryEpochStart p.i) O.H →
    Qc ≤ (F.connection w.1).scalarCurvature w.2 →
    rNext⁻¹ ^ 2 ≤ (F.connection w.1).scalarCurvature w.2 →
    SurgeryCanonicalOn F (surgeryObservationInterval O ∩ Iio w.1) rNext →
    (F.connection w.1).scalarCurvature w.2 * (w.1 - t) ∈ Icc 0 1 →
    SurgeryCanonicalControl F w.1 w.2 S.setup.epsilon S.setup.C
  have hcontrol : GuardedControl ⟨t + d / ((F.parameters.h t)⁻¹ ^ 2),
      closed.forward d htop (initial.chart z)⟩ :=
    transfer F O hH prior hadmissible hpinch (next.mono_delta (min_le_right _ _))
      (fun b hb => (overlap b hb).trans (min_le_right _ _)) t hT i (Icc 0 d)
      closed initial comparison hzero (closedBased hzero) hh d htop
      ⟨hd.le, hdTheta.le⟩ (Subset.refl _) z hzR
  have hbaseControl : GuardedControl ⟨base, y⟩ := (congrArg GuardedControl hpoint).mp hcontrol
  have hscalar : (F.connection base).scalarCurvature y = Q :=
    (H.scalar_pullback base ht x).trans hscale
  have hAgeEq : Q * (base - t) = -a := by
    dsimp only [t]
    field_simp [hQ.ne']
    ring
  have hAge : Q * (base - t) ∈ Icc 0 1 := by
    rw [hAgeEq]
    exact ⟨by linarith only [ha.2], by linarith only [ha.1, htauOne]⟩
  have hCanonical : SurgeryCanonicalControl F base y S.setup.epsilon S.setup.C := by
    apply hbaseControl hBase
    · simpa only [hscalar] using (le_max_right Qfactory Qc).trans hLarge
    · simpa only [hscalar] using hScale
    · exact hEarlier
    · simpa only [hscalar] using hAge
  have heps : F.parameters.epsilon = S.setup.epsilon := by rw [prior.epsilon_eq, hp.setup_eq]
  have hC : F.parameters.C = S.setup.C := by rw [prior.C_eq, hp.setup_eq]
  simpa only [heps, hC] using hCanonical

end PoincareConjecture.M47
