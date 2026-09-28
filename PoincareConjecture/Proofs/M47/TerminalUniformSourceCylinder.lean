import PoincareConjecture.Proofs.M47.TerminalCommonIntervalSearch
import PoincareConjecture.Proofs.M47.BlowupControlsSourceBoundedCapCanonical
import PoincareConjecture.Proofs.M47.BlowupControlsSourceZeroCapCanonical
import PoincareConjecture.Proofs.M47.BlowupControlsSourceMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

private theorem uniformSource_zero_contact
    {F : SurgeryFlowData.{u}} {base Q : ℝ} {U : Set (F.slice base).carrier}
    (e : SurgeryFlowCylinder F (F.slice base) base Q (Icc 0 0) U)
    (hbased : ∀ hs y, y ∈ U → HEq (e.forward 0 hs y) y)
    (hcontact : ∃ hT : base + 0 / Q ∈ F.surgery_times,
      ∀ [Nonempty (F.slice (base + 0 / Q)).carrier],
        ∃ i : Fin (F.event (base + 0 / Q) hT).cap_count,
          (e.forward 0 ⟨le_rfl, le_rfl⟩ '' U ∩
            ((F.event (base + 0 / Q) hT).caps i).carrier).Nonempty) :
    ∃ hT : base ∈ F.surgery_times, ∀ [Nonempty (F.slice base).carrier],
      ∃ i : Fin (F.event base hT).cap_count,
        ∃ y ∈ U, y ∈ ((F.event base hT).caps i).carrier := by
  let Contact (p : (t : ℝ) × (U → (F.slice t).carrier)) : Prop :=
    ∃ hT : p.1 ∈ F.surgery_times, ∀ [Nonempty (F.slice p.1).carrier],
      ∃ i : Fin (F.event p.1 hT).cap_count,
        (range p.2 ∩ ((F.event p.1 hT).caps i).carrier).Nonempty
  have hsource : Contact ⟨base + 0 / Q,
      fun z : U => e.forward 0 ⟨le_rfl, le_rfl⟩ z.1⟩ := by
    obtain ⟨hT, hcontact⟩ := hcontact
    refine ⟨hT, ?_⟩
    intro hn
    obtain ⟨i, z, ⟨y, hy, rfl⟩, hz⟩ := hcontact
    exact ⟨i, _, ⟨⟨y, hy⟩, rfl⟩, hz⟩
  have hmap : (⟨base + 0 / Q, fun z : U => e.forward 0 ⟨le_rfl, le_rfl⟩ z.1⟩ :
      (t : ℝ) × (U → (F.slice t).carrier)) = ⟨base, fun z : U => z.1⟩ := by
    apply Sigma.ext (by simp)
    apply Function.hfunext rfl
    intro z w hzw
    cases hzw
    exact hbased _ z.1 z.2
  have htarget : Contact ⟨base, fun z : U => z.1⟩ :=
    (congrArg Contact hmap).mp hsource
  obtain ⟨hT, htarget⟩ := htarget
  refine ⟨hT, ?_⟩
  intro hn
  obtain ⟨i, z, ⟨y, rfl⟩, hz⟩ := htarget
  exact ⟨i, y.1, y.2, hz⟩

theorem exists_first_failure_uniform_source_cylinder_of_pointwise
    (P : M46Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
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
            SurgeryCanonicalControl F base x S.setup.epsilon S.setup.C)
    {K : ℝ} (hK : 1 ≤ K) :
    ∃ tau : ℝ, 0 < tau ∧ tau ≤ 1 ∧
      ∀ A : ℝ, 0 < A → ∃ Q0 : ℝ, 0 < Q0 ∧
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
          ¬ SurgeryCanonicalControl F base (H.history.forward base ht x)
            F.parameters.epsilon F.parameters.C →
        ∀ eta : ℝ, 0 < eta → blowupPinchingThreshold (8 * K) eta ≤ Q →
          (∀ y ∈ (F.metric base).ball (H.history.forward base ht x) (A / Real.sqrt Q),
            (F.connection base).scalarCurvature y ≤ (2 * K) * Q) →
          ∃ e : SurgeryFlowCylinder F (F.slice base) base Q (Icc (-tau) 0)
              ((F.metric base).ball (H.history.forward base ht x) (A / Real.sqrt Q)),
            (∀ hs y,
              y ∈ (F.metric base).ball (H.history.forward base ht x) (A / Real.sqrt Q) →
                HEq (e.forward 0 hs y) y) ∧
            ∀ s hs y,
              y ∈ (F.metric base).ball (H.history.forward base ht x) (A / Real.sqrt Q) →
                |(F.connection (base + s / Q)).curvatureTensorNorm (e.forward s hs y)| ≤
                    (13 * max (8 * K) 1) * Q ∧
                  (F.connection (base + s / Q)).negativeCurvaturePart (e.forward s hs y) ≤
                    eta * Q := by
  let D := terminalCommonIntervalDuration S B K
  let B0 : ℝ := 13 * max (8 * K) 1
  have hD : 0 < D := (terminalCommonInterval_duration_bounds S B hK).1
  have hDOne : D ≤ 1 := (terminalCommonInterval_duration_bounds S B hK).2.1
  have hB0 : 0 < B0 := by dsimp only [B0]; positivity
  let tau := min D (12 * B0)⁻¹
  have htau : 0 < tau := lt_min hD (inv_pos.mpr (by positivity))
  have htauD : tau ≤ D := min_le_left _ _
  have htauOne : tau ≤ 1 := htauD.trans hDOne
  have hshort : 6 * B0 * tau ≤ 1 / 2 := by
    have hmul : tau * (12 * B0) ≤ 1 := (le_div_iff₀ (by positivity : 0 < 12 * B0)).mp
      (by simpa only [one_div] using (min_le_right D (12 * B0)⁻¹))
    nlinarith only [hmul]
  refine ⟨tau, htau, htauOne, fun A hA => ?_⟩
  obtain ⟨Qpositive, hQpositive, _h128, positive⟩ :=
    exists_bounded_positive_cap_canonical_cutoff P S p hp
      (by linarith only [hK] : 0 < 8 * K) hA pointwise
  obtain ⟨Qzero, _hQzero, zero⟩ :=
    exists_first_failure_zero_cap_canonical_cutoff S p hp hA pointwise
  let Q0 := max Qpositive (max Qzero (max B.curvature_threshold (64 * (2 * D + 1))))
  refine ⟨Q0, hQpositive.trans_le (le_max_left _ _), fun rNext hrNext hrLast => ?_⟩
  obtain ⟨deltaPositive, hdeltaPositive, hdeltaLast, applyPositive⟩ :=
    positive rNext hrNext hrLast
  obtain ⟨deltaZero, hdeltaZero, _hdeltaZeroLast, applyZero⟩ := zero rNext hrNext hrLast
  let cutoff := min deltaPositive (min deltaZero (B.delta S.setup.standard_initial S.constants))
  have hcutPositive : cutoff ≤ deltaPositive := min_le_left _ _
  have hcutZero : cutoff ≤ deltaZero := (min_le_right _ _).trans (min_le_left _ _)
  have hcutAnalytic : cutoff ≤ B.delta S.setup.standard_initial S.constants :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨cutoff, lt_min hdeltaPositive (lt_min hdeltaZero (B.delta_pos _ _)),
    hcutPositive.trans hdeltaLast, ?_⟩
  intro F O hH prior hadmissible hpinch next overlap W H base Q ht hBase hLarge
    hThreshold hEarlier x hscale hfail eta heta hPinchingScale hTerminal
  have hQpositiveQ : Qpositive ≤ Q := (le_max_left _ _).trans hLarge
  have hQzeroQ : Qzero ≤ Q :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hLarge)
  have hQlarge : B.curvature_threshold ≤ Q :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hLarge))
  have hQtime : 64 * (2 * D + 1) ≤ Q :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hLarge))
  have hQ : 0 < Q := hQpositive.trans_le hQpositiveQ
  have hInitial : F.standard_initial = S.setup.standard_initial := by
    rw [prior.standard_initial_eq, hp.setup_eq]
  have hC : F.parameters.C = S.setup.C := by rw [prior.C_eq, hp.setup_eq]
  have hOverlap : ∀ s ∈ surgeryObservationInterval O ∩
      Ico (surgeryEpochStart (p.i - 1)) O.H,
      F.parameters.delta s ≤ B.delta S.setup.standard_initial S.constants := by
    intro s hs
    exact (overlap s ⟨hs.1, ⟨hs.2.1, hs.2.2.trans_le hH⟩⟩).trans hcutAnalytic
  let U := (F.metric base).ball (H.history.forward base ht x) (A / Real.sqrt Q)
  have hcenter : H.history.forward base ht x ∈ U := by
    change (F.metric base).edist _ _ < ENNReal.ofReal (A / Real.sqrt Q)
    rw [M36.metric_edist_self]
    exact ENNReal.ofReal_pos.mpr (div_pos hA (Real.sqrt_pos.mpr hQ))
  obtain ⟨b, hb, e, hbased, hbounds, hstop⟩ :=
    terminalCommonInterval_exists_bounded_search S B hK p O hInitial prior.local_constants_eq
      hC hBase hQtime hQlarge hThreshold hpinch hEarlier hOverlap P U
      (M04.initial_ball_isOpen _ _ _) ⟨_, hcenter⟩ hTerminal heta hPinchingScale
  by_cases hlong : b < -tau
  · have htime : Icc (-tau) 0 ⊆ Icc b 0 := Icc_subset_Icc hlong.le le_rfl
    refine ⟨e.restrict htime ordConnected_Icc (Subset.refl _),
      fun hs y hy => hbased (htime hs) y hy, ?_⟩
    intro s hs y hy
    exact (hbounds s (htime hs) y hy).2
  · have hnear : -tau ≤ b := le_of_not_gt hlong
    have hcap := hstop.resolve_left (by
      intro hbD
      exact hlong (hbD.trans_le (neg_le_neg htauD)))
    by_cases hbNeg : b < 0
    · have ha : b ∈ Ico (-1 : ℝ) 0 := ⟨by linarith only [hnear, htauOne], hbNeg⟩
      have hmetric := normalized_search_metric_comparison ⟨P.m04, P.m13.ordinary_flow⟩
        hpinch e (M04.initial_ball_isOpen _ _ _) hb.2 hB0.le hbased
        (fun s hs y hy => (le_abs_self _).trans (hbounds s hs y hy).2.1)
        ((mul_le_mul_of_nonneg_left (by linarith only [hnear] : -b ≤ tau)
          (by positivity : 0 ≤ 6 * B0)).trans hshort)
      obtain ⟨hT, hcap⟩ := hcap.2
      let _inst : Nonempty (F.slice (base + b / Q)).carrier :=
        ⟨e.forward b ⟨le_rfl, hb.2⟩ (H.history.forward base ht x)⟩
      obtain ⟨i, z, ⟨contact, hcontact, rfl⟩, hc⟩ := hcap
      exact (hfail (applyPositive F O hH prior hadmissible hpinch
        (next.mono_delta hcutPositive) (fun s hs => (overlap s hs).trans hcutPositive)
        hBase hQpositiveQ hThreshold hEarlier ha (H.history.forward base ht x)
        ((H.scalar_pullback base ht x).trans hscale) e hbased
        (fun s hs y hy => (hbounds s hs y hy).1)
        (fun y hy v => (hmetric b ⟨le_rfl, hb.2⟩ y hy v).2)
        hT i contact hcontact hc)).elim
    · have hbZero : b = 0 := le_antisymm hb.2 (le_of_not_gt hbNeg)
      subst b
      obtain ⟨hT, contact⟩ := uniformSource_zero_contact e hbased hcap.2
      let _inst : Nonempty (F.slice base).carrier := ⟨H.history.forward base ht x⟩
      obtain ⟨i, y, hy, hcapY⟩ := contact
      exact (hfail (applyZero F O hH prior hadmissible hpinch
        (next.mono_delta hcutZero) (fun s hs => (overlap s hs).trans hcutZero)
        W H ht hBase hQzeroQ hThreshold hEarlier x hscale hT i y hy hcapY)).elim

end PoincareConjecture.M47
