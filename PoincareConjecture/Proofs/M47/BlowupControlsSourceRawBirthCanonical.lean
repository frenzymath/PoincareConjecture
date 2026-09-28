import PoincareConjecture.Proofs.M47.BlowupControlsSourceCompactCanonical
import PoincareConjecture.Proofs.M47.BlowupControlsSourceBirth
import PoincareConjecture.Proofs.M47.BlowupControlsSourceBirthCenter











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

theorem exists_first_failure_raw_birth_cap_canonical_cutoff
    (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
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
        ∀ {base Q : ℝ}, base ∈ Ico (surgeryEpochStart p.i) O.H →
          Q0 ≤ Q → rNext⁻¹ ^ 2 ≤ Q →
          SurgeryCanonicalOn F (surgeryObservationInterval O ∩ Iio base) rNext →
          ∀ x : (F.slice base).carrier, (F.connection base).scalarCurvature x = Q →
          ∀ hT : base ∈ F.surgery_times, ∀ [Nonempty (F.slice base).carrier],
          ∀ i : Fin (F.event base hT).cap_count,
            x ∈ ((F.event base hT).caps i).carrier →
            SurgeryCanonicalControl F base x F.parameters.epsilon F.parameters.C := by
  let R : ℝ := S.standard_initial.cylindrical_end.radius + 6
  have hR : 0 < R := by
    dsimp only [R]
    linarith [S.standard_initial.cylindrical_end.radius_pos]
  obtain ⟨Amin, etaMin, Q0, hAmin, hRcompact, hetaMin, hetaSmall, hQ0, compact⟩ :=
    exists_compact_source_standard_canonical_transfer S p (theta := 0) (R := 2 * R)
      (by positivity) (fun v hv z => pointwise 0 (by norm_num) v hv z)
  let eta := etaMin
  obtain ⟨deltaBirth, hdeltaBirth, birth⟩ :=
    exists_cap_birth_family_comparison_cutoff S.standard_initial S.constants hAmin hetaMin
  refine ⟨Q0, hQ0, ?_⟩
  intro rNext hrNext hrLast
  obtain ⟨deltaCompact, hdeltaCompact, hdeltaCompactLast, transfer⟩ :=
    compact Amin le_rfl eta hetaMin le_rfl rNext hrNext hrLast
  let cutoff := min deltaBirth deltaCompact
  refine ⟨cutoff, lt_min hdeltaBirth hdeltaCompact,
    (min_le_right _ _).trans hdeltaCompactLast, ?_⟩
  intro F O hH prior hadmissible hpinch next overlap base Q hBase hLarge hScale hEarlier
    x hscalar hT hn i hcap
  have hInitial : F.standard_initial = S.standard_initial := by
    rw [prior.standard_initial_eq, hp.setup_eq]
    exact S.setup_standard_initial_eq
  have hConstants : F.local_constants = S.constants := prior.local_constants_eq
  have hepsilon : F.parameters.epsilon = S.setup.epsilon := by
    rw [prior.epsilon_eq, hp.setup_eq]
  have hC : F.parameters.C = S.setup.C := by rw [prior.C_eq, hp.setup_eq]
  have hmodel : HEq (O.redecorateTo prior.standard_initial_eq).standard_flow
      S.cap_persistence.standard_cap.flow := by
    apply (Proofs.M46.redecorateTo_standard_flow O prior.standard_initial_eq).trans
    rw [hp.setup_eq]
    exact S.setup_standard_flow_eq
  have hbasePos : 0 < base :=
    (show 0 < surgeryEpochStart p.i by unfold surgeryEpochStart; positivity).trans_le hBase.1
  have hdelta : F.parameters.delta base ≤ deltaBirth :=
    (next.delta_le base ⟨⟨hbasePos.le, hBase.2⟩, hBase.1⟩).trans (min_le_left _ _)
  have hlifetime : (O.redecorateTo prior.standard_initial_eq).standard_flow.base.lifetime = 1 := by
    have hpair : (⟨F.standard_initial, (O.redecorateTo prior.standard_initial_eq).standard_flow⟩ :
        Σ g : StandardInitialMetric, MaximalStandardCapFlow g) =
        ⟨S.standard_initial, S.cap_persistence.standard_cap.flow⟩ :=
      Sigma.ext hInitial hmodel
    exact (congrArg (fun p : Σ g : StandardInitialMetric, MaximalStandardCapFlow g =>
      p.2.base.lifetime) hpair).trans S.cap_persistence.standard_cap.lifetime_one
  obtain ⟨e, initial, comparison, based⟩ :=
    birth F hInitial hConstants (O.redecorateTo prior.standard_initial_eq).standard_flow
      hlifetime base hT hdelta i
  have hh : 0 < F.parameters.h base :=
    F.parameters.h_pos base (F.time_domain_nonnegative (F.surgery_times_subset hT))
  have houter := ((F.event base hT).caps i).outer_ball hcap
  have hrad : F.standard_initial.cylindrical_end.radius =
      S.standard_initial.cylindrical_end.radius :=
    congrArg (fun g : StandardInitialMetric => g.cylindrical_end.radius) hInitial
  change (F.metric base).edist ((F.event base hT).caps i).tip x ≤
    ENNReal.ofReal (F.parameters.h base *
      (F.standard_initial.cylindrical_end.radius + 5)) at houter
  have hcapBall : x ∈ (F.metric base).ball ((F.event base hT).caps i).tip
      (R * F.parameters.h base) := by
    change (F.metric base).edist ((F.event base hT).caps i).tip x <
      ENNReal.ofReal (R * F.parameters.h base)
    apply lt_of_le_of_lt houter
    apply (ENNReal.ofReal_lt_ofReal_iff (mul_pos hR hh)).mpr
    rw [hrad]
    dsimp only [R]
    nlinarith only [hh, S.standard_initial.cylindrical_end.radius_pos]
  have hzero : (0 : ℝ) ∈ Icc 0 0 := ⟨le_rfl, le_rfl⟩
  obtain ⟨z, hz, hzx, hzR⟩ := exists_cap_birth_center_in_fixed_ball hR
    (by linarith only [hR, hRcompact]) hetaMin hetaSmall e initial comparison
      hzero (based _) hcapBall
  have hzRadius : S.standard_initial.metric.edist 0 z ≤ ENNReal.ofReal (2 * R) := by
    simpa only [hInitial] using hzR
  have hzSource : initial.chart z ∈
      (F.metric base).ball ((F.event base hT).caps i).tip
        (Amin * F.parameters.h base) :=
    comparison.choose_spec.2.2.2.1 ▸ mem_image_of_mem initial.chart hz
  have hpoint : (⟨base + 0 / ((F.parameters.h base)⁻¹ ^ 2),
      e.forward 0 hzero (initial.chart z)⟩ : Σ s, (F.slice s).carrier) = ⟨base, x⟩ := by
    apply Sigma.ext (by simp)
    exact (based hzero (initial.chart z) hzSource).trans (heq_of_eq hzx)
  let GuardedControl (w : Σ s, (F.slice s).carrier) : Prop :=
    w.1 ∈ Ico (surgeryEpochStart p.i) O.H →
    Q0 ≤ (F.connection w.1).scalarCurvature w.2 →
    rNext⁻¹ ^ 2 ≤ (F.connection w.1).scalarCurvature w.2 →
    SurgeryCanonicalOn F (surgeryObservationInterval O ∩ Iio w.1) rNext →
    (F.connection w.1).scalarCurvature w.2 * (w.1 - base) ∈ Icc 0 1 →
    SurgeryCanonicalControl F w.1 w.2 S.setup.epsilon S.setup.C
  have hcontrol : GuardedControl ⟨base + 0 / ((F.parameters.h base)⁻¹ ^ 2),
      e.forward 0 hzero (initial.chart z)⟩ :=
    transfer F O hH prior hadmissible hpinch
      (next.mono_delta (min_le_right _ _))
      (fun b hb => (overlap b hb).trans (min_le_right _ _)) base hT i (Icc 0 0)
      e initial comparison hzero (based hzero) hh 0 hzero hzero (Subset.refl _) z hzRadius
  have hbaseControl : GuardedControl ⟨base, x⟩ := (congrArg GuardedControl hpoint).mp hcontrol
  have hcanonical : SurgeryCanonicalControl F base x S.setup.epsilon S.setup.C := by
    apply hbaseControl hBase
    · simpa only [hscalar] using hLarge
    · simpa only [hscalar] using hScale
    · exact hEarlier
    · simp
  simpa only [hepsilon, hC] using hcanonical

end PoincareConjecture.M47
