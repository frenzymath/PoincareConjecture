import PoincareConjecture.Proofs.M47.SeedBufferedSequence
import PoincareConjecture.Proofs.M47.SeedBadPointHistory
import PoincareConjecture.Proofs.M47.SeedPreliminaryVolume
import PoincareConjecture.Proofs.M47.BlowupControlsSourceRawBirthCanonical
import PoincareConjecture.Proofs.M47.BlowupControlsSourceCanonicalCylinder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology

universe u

namespace PoincareConjecture.Proofs.M47

open PoincareConjecture.M47

theorem exists_seed_regular_counterexample_sequence_of_pointwise
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (N : RepairedNoncollapseInductionData S)
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
    (hno : ¬ Nonempty (SurgeryCanonicalExtension p (Classical.choice (N.induction p hp)))) :
    ∃ k : ℝ, 0 < k ∧ ∀ c : ℕ → ℝ, (∀ n, 0 < c n) →
      ∃ (n0 : ℕ) (r delta : ℕ → ℝ) (F : ℕ → SurgeryFlowData.{u})
        (O : ∀ n, SurgeryObservation (F n)) (t : ℕ → ℝ)
        (W : ∀ n, M33RegularHistoryWindow (F n))
        (H : ∀ n, M33RegularHistoryData (W n))
        (ht : ∀ n, t n ∈ (H n).generalized.interval)
        (y : ∀ n, ((H n).generalized.slice (t n)).carrier),
      ∃ (hPositive : ∀ n, 0 < ((F n).connection (t n)).scalarCurvature
          ((H n).history.forward (t n) (ht n) (y n)))
        (hDiverges : Tendsto (fun n => ((F n).connection (t n)).scalarCurvature
          ((H n).history.forward (t n) (ht n) (y n))) atTop atTop),
        Tendsto r atTop (𝓝 0) ∧ Tendsto delta atTop (𝓝 0) ∧
        (∀ n, r n = p.r (Fin.last p.i) / ((n + n0 : ℕ) + 1 : ℝ) ∧
          (W n).interval = Icc 0 (t n) ∧
          0 < r n ∧ r n ≤ p.r (Fin.last p.i) ∧
          0 < delta n ∧ delta n ≤ c (n + n0) ∧
          delta n ≤ (Classical.choice (N.induction p hp)).cutoff (r n) ∧
          SurgeryObservationIsNextEpoch p (O n) ∧ SurgeryPrefixControls p (F n) (O n) ∧
          SurgeryFlowAdmissible (F n) ∧ SurgeryFlowPinched (F n) ∧
          SurgeryFlowTerminalPolicyOn (F n) (surgeryObservationInterval (O n)) ∧
          SurgeryPostPrefixScales p (F n) (O n) (r n) (delta n) ∧
          (∀ s ∈ surgeryObservationInterval (O n) ∩
            Ico (surgeryEpochStart (p.i - 1)) (O n).H, (F n).parameters.delta s ≤ delta n) ∧
          t n ∈ Ico (surgeryEpochStart p.i) (O n).H ∧
          t n = sInf (canonicalFailureTimes (F n) (O n) (r n)) ∧
          SurgeryCanonicalOn (F n) (Ico 0 (t n)) (r n) ∧
          (r n)⁻¹ ^ 2 ≤ ((F n).connection (t n)).scalarCurvature
            ((H n).history.forward (t n) (ht n) (y n)) ∧
          ¬ SurgeryCanonicalControl (F n) (t n)
            ((H n).history.forward (t n) (ht n) (y n))
            (F n).parameters.epsilon (F n).parameters.C ∧
          SurgeryVolumeControlOn (F n) (Icc (surgeryEpochStart p.i - 1 / 128) (t n)) k
            (fun _ _ => True)) ∧
        let V := regularHistoryBlowupSequence F W H t ht y hPositive hDiverges
        ∃ rho v : ℝ, 0 < rho ∧ 0 < v ∧ ∀ᶠ n in atTop,
          ENNReal.ofReal (v / (Real.sqrt (V.scale n)) ^ 3) ≤
            calibratedMetricVolume ((V.flow n).metric (V.base n).1) (V.baseBall n rho) := by
  classical
  obtain ⟨Qbirth, _hQbirth, birth⟩ :=
    exists_first_failure_raw_birth_cap_canonical_cutoff S p hp pointwise
  obtain ⟨Qcyl, tau, K, _hQcyl, htau, _htauOne, hK, cylinder⟩ :=
    exists_first_failure_source_cylinder_of_pointwise P.toM46 S B p hp
      (by norm_num : (0 : ℝ) < 1) pointwise
  let Q0 := max Qbirth Qcyl
  obtain ⟨k, hk, sequence⟩ := exists_seed_buffered_counterexample_sequence P S N p hp hno
  refine ⟨k, hk, ?_⟩
  intro c hc
  let r0 : ℕ → ℝ := fun n => p.r (Fin.last p.i) / ((n : ℝ) + 1)
  have hr0 (n : ℕ) : 0 < r0 n ∧ r0 n ≤ p.r (Fin.last p.i) :=
    canonicalInduction_radius_bounds (p.r_pos _) n
  choose dBirth hdBirth _hdBirthLast applyBirth using
    fun n => birth (r0 n) (hr0 n).1 (hr0 n).2
  choose dCyl hdCyl _hdCylLast applyCylinder using
    fun n => cylinder (r0 n) (hr0 n).1 (hr0 n).2
  let cutoff : ℕ → ℝ := fun n => min (c n) (min (dBirth n) (dCyl n))
  have hcutoff (n : ℕ) : 0 < cutoff n := lt_min (hc n) (lt_min (hdBirth n) (hdCyl n))
  obtain ⟨rRaw, dRaw, FRaw, ORaw, tRaw, xRaw, hrRaw, hrLimit, hdLimit, hQlimit, data⟩ :=
    sequence cutoff hcutoff
  have hrEq (n : ℕ) : rRaw n = r0 n := hrRaw n
  have hlarge : ∀ᶠ n in atTop,
      Q0 ≤ ((FRaw n).connection (tRaw n)).scalarCurvature (xRaw n) :=
    hQlimit.eventually (eventually_ge_atTop Q0)
  obtain ⟨n0, hn0⟩ := eventually_atTop.1 hlarge
  let shift : ℕ → ℕ := fun n => n + n0
  have hshift : Tendsto shift atTop atTop :=
    (show StrictMono shift from fun _ _ h => Nat.add_lt_add_right h n0).tendsto_atTop
  let r := rRaw ∘ shift
  let delta := dRaw ∘ shift
  let F := FRaw ∘ shift
  let O : ∀ n, SurgeryObservation (F n) := fun n => ORaw (shift n)
  let t := tRaw ∘ shift
  let x : ∀ n, ((F n).slice (t n)).carrier := fun n => xRaw (shift n)
  have tpos (n : ℕ) : 0 < t n := by
    rcases data (shift n) with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hbase, _⟩
    exact (show 0 < surgeryEpochStart p.i by unfold surgeryEpochStart; positivity).trans_le
      hbase.1
  have tmem (n : ℕ) : t n ∈ (F n).time_domain := by
    rcases data (shift n) with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hbase, _⟩
    exact (O n).interval_subset ⟨(tpos n).le, hbase.2⟩
  let W (n : ℕ) := (F n).closedRegularHistoryWindow (t n) (tpos n) (tmem n) ⟨x n⟩
  let H : ∀ n, M33RegularHistoryData (W n) :=
    fun n => Classical.choice (P.regular_history (F n) (W n))
  have ht (n : ℕ) : t n ∈ (H n).generalized.interval := by
    rw [(H n).interval_eq]
    exact ⟨(tpos n).le, le_rfl⟩
  have preimage (n : ℕ) : ∃ y : ((H n).generalized.slice (t n)).carrier,
      (H n).history.forward (t n) (ht n) y = x n := by
    rcases data (shift n) with
      ⟨_hr, _hrLast, _hd, hcut, _hN, hnext, old, hadmissible, hpinch,
        _hpolicy, scales, overlap, hbase, _hinf, past, high, bad, _vol⟩
    apply exists_first_failure_history_preimage (H n) (ht n) (x n) bad
    have hdB : dRaw (shift n) ≤ dBirth (shift n) :=
      hcut.trans ((min_le_right _ _).trans (min_le_left _ _))
    have highB := (le_max_left Qbirth Qcyl).trans (hn0 (shift n) (Nat.le_add_left n0 n))
    apply applyBirth (shift n) (F n) (O n) hnext.2 old hadmissible hpinch
      (by rw [← hrEq]; exact scales.mono_delta hdB)
      (fun s hs => (overlap s ⟨hs.1, hs.2.1, hs.1.2⟩).trans hdB)
      hbase highB (by simpa only [← hrEq] using high)
      (fun s hs hsF z hz => past s ⟨hs.1.1, hs.2⟩ hsF z (by
        rw [hrEq]; exact hz)) (x n) rfl
  choose y hy using preimage
  have hPositive (n : ℕ) : 0 < ((F n).connection (t n)).scalarCurvature
      ((H n).history.forward (t n) (ht n) (y n)) := by
    rw [hy n]
    rcases data (shift n) with
      ⟨hr, _, _, _, _, _, _, _, _, _, _, _, _, _, _, high, _⟩
    exact (sq_pos_of_pos (inv_pos.mpr hr)).trans_le high
  have hDiverges : Tendsto (fun n => ((F n).connection (t n)).scalarCurvature
      ((H n).history.forward (t n) (ht n) (y n))) atTop atTop := by
    have heq : (fun n => ((F n).connection (t n)).scalarCurvature
        ((H n).history.forward (t n) (ht n) (y n))) =
        (fun n => ((FRaw (shift n)).connection (tRaw (shift n))).scalarCurvature
          (xRaw (shift n))) := by
      funext n
      rw [hy n]
      rfl
    rw [heq]
    exact hQlimit.comp hshift
  refine ⟨n0, r, delta, F, O, t, W, H, ht, y, hPositive, hDiverges,
    hrLimit.comp hshift, hdLimit.comp hshift, ?_, ?_⟩
  · intro n
    rcases data (shift n) with
      ⟨hr, hrLast, hd, hcut, hN, hnext, old, hadmissible, hpinch,
        hpolicy, scales, overlap, hbase, hinf, past, high, bad, vol⟩
    refine ⟨hrRaw (shift n), rfl, hr, hrLast, hd, hcut.trans (min_le_left _ _),
      hN, hnext, old, hadmissible, hpinch, hpolicy, scales, overlap, hbase, hinf,
      past, ?_, ?_, vol⟩
    · rw [hy n]
      exact high
    · rw [hy n]
      exact bad
  · let V := regularHistoryBlowupSequence F W H t ht y hPositive hDiverges
    have hscale (n : ℕ) : (H n).generalized.scalar ⟨t n, y n⟩ =
        ((F n).connection (t n)).scalarCurvature (x n) := by
      change ((H n).generalized.connection (t n)).scalarCurvature (y n) = _
      rw [← (H n).scalar_pullback (t n) (ht n), hy n]
    have cylinders : ∀ n,
        ∃ e : SurgeryFlowCylinder (F n) ((F n).slice (t n)) (t n) (V.scale n)
            (Icc (-tau) 0) (((F n).metric (t n)).ball
              ((H n).history.forward (t n) (ht n) (y n)) (1 / Real.sqrt (V.scale n))),
          (∀ hs z, z ∈ ((F n).metric (t n)).ball
            ((H n).history.forward (t n) (ht n) (y n)) (1 / Real.sqrt (V.scale n)) →
              HEq (e.forward 0 hs z) z) ∧
          ∀ s hs z, z ∈ ((F n).metric (t n)).ball
              ((H n).history.forward (t n) (ht n) (y n)) (1 / Real.sqrt (V.scale n)) →
            ((F n).connection (t n + s / V.scale n)).curvatureTensorNorm
              (e.forward s hs z) ≤ K * V.scale n := by
      intro n
      rcases data (shift n) with
        ⟨_hr, _hrLast, _hd, hcut, _hN, hnext, old, hadmissible, hpinch,
          _hpolicy, scales, overlap, hbase, _hinf, past, high, bad, _vol⟩
      have hdC : dRaw (shift n) ≤ dCyl (shift n) :=
        hcut.trans ((min_le_right _ _).trans (min_le_right _ _))
      have highC : Qcyl ≤ V.scale n := by
        change Qcyl ≤ (H n).generalized.scalar ⟨t n, y n⟩
        rw [hscale]
        exact (le_max_right Qbirth Qcyl).trans (hn0 (shift n) (Nat.le_add_left n0 n))
      apply applyCylinder (shift n) (F n) (O n) hnext.2 old hadmissible hpinch
        (by rw [← hrEq]; exact scales.mono_delta hdC)
        (fun s hs => (overlap s ⟨hs.1, hs.2.1, hs.1.2⟩).trans hdC)
        (W n) (H n) (ht n) hbase highC
      · change (r0 (shift n))⁻¹ ^ 2 ≤ (H n).generalized.scalar ⟨t n, y n⟩
        rw [hscale, ← hrEq]
        exact high
      · intro s hs hsF z hz
        exact past s ⟨hs.1.1, hs.2⟩ hsF z (by rw [hrEq]; exact hz)
      · exact rfl
      · rw [hy n]
        exact bad
    have hEpsilon (n : ℕ) : (F n).parameters.epsilon = S.setup.epsilon := by
      rcases data (shift n) with ⟨_, _, _, _, _, _, old, _⟩
      change (FRaw (shift n)).parameters.epsilon = S.setup.epsilon
      rw [old.epsilon_eq, hp.setup_eq]
    have hvolume : ∀ᶠ n in atTop,
        SurgeryVolumeControlOn (F n) (Icc (surgeryEpochStart p.i - 1 / 128) (t n)) k
          (fun _ _ => True) ∧ t n ∈ Icc (surgeryEpochStart p.i - 1 / 128) (t n) := by
      apply Eventually.of_forall
      intro n
      rcases data (shift n) with
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, hbase, _, _, _, _, vol⟩
      refine ⟨vol, ?_, le_rfl⟩
      exact (sub_le_self _ (by norm_num : (0 : ℝ) ≤ 1 / 128)).trans hbase.1
    exact seed_preliminary_sequence_terminal_volume F W H t ht y hPositive hDiverges
      hk (by norm_num : (0 : ℝ) < 1) htau hK.le S.setup.epsilon_pos hEpsilon
      (fun n => Icc (surgeryEpochStart p.i - 1 / 128) (t n)) hvolume
      (Eventually.of_forall cylinders)

end PoincareConjecture.Proofs.M47
