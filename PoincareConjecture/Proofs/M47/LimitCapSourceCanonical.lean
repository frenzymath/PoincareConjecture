import PoincareConjecture.Proofs.M47.LimitCapSourcePrefix
import PoincareConjecture.Proofs.M47.BlowupControlsSourceCompactLongCanonical
import PoincareConjecture.Proofs.M47.BlowupControlsSourceBirthCenter

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

theorem exists_finite_source_cap_canonical_cutoff
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    {T K D : ℝ} (hT : 0 ≤ T) (hK : 0 < K) (hD : 0 ≤ D) :
    ∃ Q0 : ℝ, 0 < Q0 ∧ 64 * (T + 1) ≤ Q0 ∧
      ∀ rNext : ℝ, 0 < rNext → rNext ≤ p.r (Fin.last p.i) →
        ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
        ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
          O.H ≤ surgeryEpochStart (p.i + 1) →
        ∀ _prior : SurgeryPrefixControls p F O,
          SurgeryFlowAdmissible F → SurgeryFlowPinched F →
          SurgeryPostPrefixScales p F O rNext cutoff →
          (∀ s ∈ surgeryObservationInterval O ∩ overlapInterval p,
            F.parameters.delta s ≤ cutoff) →
        ∀ {base Q : ℝ}, base ∈ Ico (surgeryEpochStart p.i) O.H → Q0 ≤ Q →
          rNext⁻¹ ^ 2 ≤ Q →
          SurgeryCanonicalOn F (surgeryObservationInterval O ∩ Iio base) rNext →
        ∀ (C : GeneralizedSliceCarrier.{u}) {U : Set C.carrier} (_hU : IsOpen U)
          {a : ℝ} (ha : a ∈ Ico (-T) 0),
        ∀ E : SurgeryFlowCylinder F C base Q (Icc a 0) U,
          (∀ s (hs : s ∈ Icc a 0), ∀ x ∈ U,
            (F.connection (base + s / Q)).scalarCurvature (E.forward s hs x) ≤ K * Q) →
          let bottom : a ∈ Icc a 0 := ⟨le_rfl, ha.2.le⟩
          let zero : (0 : ℝ) ∈ Icc a 0 := ⟨ha.2.le, le_rfl⟩
          let t := base + a / Q
          ∀ (hEvent : t ∈ F.surgery_times), ∀ [Nonempty (F.slice t).carrier],
          ∀ (i : Fin (F.event t hEvent).cap_count) (contact : C.carrier),
            contact ∈ U → E.forward a bottom contact ∈ ((F.event t hEvent).caps i).carrier →
            (∀ x ∈ U, (F.metric t).edist (E.forward a bottom contact)
              (E.forward a bottom x) ≤ ENNReal.ofReal (D / Real.sqrt Q)) →
            ∀ y ∈ U,
              (F.connection (base + 0 / Q)).scalarCurvature (E.forward 0 zero y) = Q →
              SurgeryCanonicalControl F (base + 0 / Q) (E.forward 0 zero y)
                F.parameters.epsilon F.parameters.C := by
  obtain ⟨theta1, theta2, Rcap, htheta1, htheta12, htheta2, hRcap, radii⟩ :=
    exists_prefix_finite_source_included_cap_cutoff P.toM46 S p hp hT hK hD
  have hR : 0 < Rcap := by linarith [S.standard_initial.cylindrical_end.radius_pos]
  obtain ⟨Ac, etaC, Qc, _hAc, _hRAc, hetaC, hetaCSmall, hQc, compact⟩ :=
    exists_compact_source_standard_unrestricted_canonical_transfer P S B p hp
      (htheta12.trans htheta2) (by positivity : 0 < 2 * Rcap)
  obtain ⟨A, etaI, hAcA, hRA, _hA, hetaI, _hetaIHalf, factory⟩ := radii Ac
  let eta := min etaI etaC
  have heta : 0 < eta := lt_min hetaI hetaC
  have hetaSmall : eta ≤ 1 / 1000 := (min_le_right _ _).trans hetaCSmall
  refine ⟨max (64 * (T + 1)) Qc, hQc.trans_le (le_max_right _ _), le_max_left _ _, ?_⟩
  intro rNext hrNext hrLast
  obtain ⟨deltaI, hdeltaI, hdeltaILast, included⟩ :=
    factory eta heta (min_le_left _ _) rNext hrNext hrLast
  obtain ⟨deltaC, hdeltaC, _hdeltaCLast, transfer⟩ :=
    compact A hAcA.le eta heta (min_le_right _ _) rNext hrNext hrLast
  refine ⟨min deltaI deltaC, lt_min hdeltaI hdeltaC,
    (min_le_left _ _).trans hdeltaILast, ?_⟩
  intro F O hH prior hadmissible hpinch next overlap base Q hBase hLarge
    hScale hEarlier C U hU a ha E hscalarBound
  dsimp only
  intro hEvent hn i contact hcontact hcap hdistance y hy hscale
  obtain ⟨hd, hdTheta, closed, initial, comparison, closedBased, captured,
    _included, top⟩ := included F O hH prior hadmissible hpinch
      (next.mono_delta (min_le_left _ _))
      (fun s hs => (overlap s hs).trans (min_le_left _ _)) hBase
      ((le_max_left _ _).trans hLarge) hEarlier C hU ha E hscalarBound
      hEvent i contact hcontact hcap hdistance
  let t := base + a / Q
  let d := (base - t) / (F.parameters.h t) ^ 2
  have hzero : (0 : ℝ) ∈ Icc 0 d := ⟨le_rfl, hd.le⟩
  have htop : d ∈ Icc 0 d := ⟨hd.le, le_rfl⟩
  let zero : (0 : ℝ) ∈ Icc a 0 := ⟨ha.2.le, le_rfl⟩
  obtain ⟨z, _hz, hzy, hzRadius⟩ := exists_cap_birth_center_in_fixed_ball
    hR hRA.le heta hetaSmall closed initial comparison hzero
      (closedBased hzero) (captured y hy)
  have hinitial : F.standard_initial = S.standard_initial := by
    rw [prior.standard_initial_eq, hp.setup_eq]
    exact S.setup_standard_initial_eq
  have hzR : S.standard_initial.metric.edist 0 z ≤ ENNReal.ofReal (2 * Rcap) := by
    simpa only [hinitial] using hzRadius
  have hh : 0 < F.parameters.h t :=
    F.parameters.h_pos t (F.time_domain_nonnegative (F.surgery_times_subset hEvent))
  have hclock : t + d / ((F.parameters.h t)⁻¹ ^ 2) = base := by
    rw [surgeryCap_physical_time]
    dsimp only [d]
    rw [div_mul_cancel₀ _ (sq_pos_of_pos hh).ne']
    ring
  have hpoint : (⟨t + d / ((F.parameters.h t)⁻¹ ^ 2),
      closed.forward d htop (initial.chart z)⟩ : Σ s, (F.slice s).carrier) =
        ⟨base + 0 / Q, E.forward 0 zero y⟩ := by
    apply Sigma.ext (hclock.trans (by simp))
    rw [hzy]
    exact top htop zero y hy
  let GuardedControl (w : Σ s, (F.slice s).carrier) : Prop :=
    w.1 ∈ Ico (surgeryEpochStart p.i) O.H →
    Qc ≤ (F.connection w.1).scalarCurvature w.2 →
    rNext⁻¹ ^ 2 ≤ (F.connection w.1).scalarCurvature w.2 →
    SurgeryCanonicalOn F (surgeryObservationInterval O ∩ Iio w.1) rNext →
    SurgeryCanonicalControl F w.1 w.2 S.setup.epsilon S.setup.C
  have hcontrol : GuardedControl ⟨t + d / ((F.parameters.h t)⁻¹ ^ 2),
      closed.forward d htop (initial.chart z)⟩ :=
    transfer F O hH prior hadmissible hpinch (next.mono_delta (min_le_right _ _))
      (fun s hs => (overlap s hs).trans (min_le_right _ _)) t hEvent i (Icc 0 d)
      closed initial comparison hzero (closedBased hzero) hh d htop
      ⟨hd.le, hdTheta.le⟩ (Subset.refl _) z hzR
  have hbaseControl : GuardedControl ⟨base + 0 / Q, E.forward 0 zero y⟩ :=
    (congrArg GuardedControl hpoint).mp hcontrol
  have hCanonical : SurgeryCanonicalControl F (base + 0 / Q) (E.forward 0 zero y)
      S.setup.epsilon S.setup.C := by
    apply hbaseControl
    · simpa only [zero_div, add_zero] using hBase
    · simpa only [hscale] using (le_max_right (64 * (T + 1)) Qc).trans hLarge
    · simpa only [hscale] using hScale
    · simpa only [zero_div, add_zero] using hEarlier
  have heps : F.parameters.epsilon = S.setup.epsilon := by rw [prior.epsilon_eq, hp.setup_eq]
  have hC : F.parameters.C = S.setup.C := by rw [prior.C_eq, hp.setup_eq]
  simpa only [heps, hC] using hCanonical

end PoincareConjecture.M47
