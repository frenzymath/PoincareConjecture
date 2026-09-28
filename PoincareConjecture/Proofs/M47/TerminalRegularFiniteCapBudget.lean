import PoincareConjecture.Proofs.M47.TerminalRegularCommonBudget
import PoincareConjecture.Proofs.M47.SourceCanonical
import PoincareConjecture.Proofs.M47.LimitCapSourceCanonical

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology

universe u

namespace PoincareConjecture.M47

theorem terminalSource_exists_regular_sequence_finite_cap_budget
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (N : RepairedNoncollapseInductionData S)
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    (A : ℕ → ℝ) (hA : ∀ j, 0 < A j)
    (hno : ¬ Nonempty (SurgeryCanonicalExtension p (Classical.choice (N.induction p hp)))) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∃ tau K duration : ℕ → ℝ,
      (∀ j, 0 < tau j ∧ tau j ≤ 1 ∧ 0 < K j) ∧
      (∀ m, 0 < duration m ∧ duration m ≤ 1) ∧
      ∀ c : ℕ → ℝ, (∀ n, 0 < c n) →
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
          t n = sInf (Proofs.M47.canonicalFailureTimes (F n) (O n) (r n)) ∧
          SurgeryCanonicalOn (F n) (Ico 0 (t n)) (r n) ∧
          (r n)⁻¹ ^ 2 ≤ ((F n).connection (t n)).scalarCurvature
            ((H n).history.forward (t n) (ht n) (y n)) ∧
          ¬ SurgeryCanonicalControl (F n) (t n)
            ((H n).history.forward (t n) (ht n) (y n))
            (F n).parameters.epsilon (F n).parameters.C ∧
          SurgeryVolumeControlOn (F n) (Icc (surgeryEpochStart p.i - 1 / 128) (t n)) kappa
            (fun _ _ => True)) ∧
        let V := regularHistoryBlowupSequence F W H t ht y hPositive hDiverges
        (∃ rho v : ℝ, 0 < rho ∧ 0 < v ∧ ∀ᶠ n in atTop,
          ENNReal.ofReal (v / (Real.sqrt (V.scale n)) ^ 3) ≤
            calibratedMetricVolume ((V.flow n).metric (V.base n).1) (V.baseBall n rho)) ∧
        (∃ sigma : ℕ → ℕ, StrictMono sigma ∧ ∀ k j, j ≤ k →
          ∃ e : SurgeryFlowCylinder (F (sigma k)) ((F (sigma k)).slice (t (sigma k)))
              (t (sigma k)) (V.scale (sigma k)) (Icc (-(tau j)) 0)
              (((F (sigma k)).metric (t (sigma k))).ball
                ((H (sigma k)).history.forward (t (sigma k)) (ht (sigma k)) (y (sigma k)))
                (A j / Real.sqrt (V.scale (sigma k)))),
            (∀ hs z, z ∈ ((F (sigma k)).metric (t (sigma k))).ball
                ((H (sigma k)).history.forward (t (sigma k)) (ht (sigma k)) (y (sigma k)))
                (A j / Real.sqrt (V.scale (sigma k))) → HEq (e.forward 0 hs z) z) ∧
            ∀ s hs z, z ∈ ((F (sigma k)).metric (t (sigma k))).ball
                ((H (sigma k)).history.forward (t (sigma k)) (ht (sigma k)) (y (sigma k)))
                (A j / Real.sqrt (V.scale (sigma k))) →
              ((F (sigma k)).connection (t (sigma k) + s / V.scale (sigma k))).curvatureTensorNorm
                (e.forward s hs z) ≤ K j * V.scale (sigma k)) ∧
        (∀ (sigma : ℕ → ℕ) (hsigma : StrictMono sigma) (m : ℕ),
          (∀ a : ℝ, 0 < a → ∀ᶠ k in atTop,
            ∀ z ∈ ((F (sigma k)).metric (t (sigma k))).ball
                ((H (sigma k)).history.forward (t (sigma k)) (ht (sigma k)) (y (sigma k)))
                (a / Real.sqrt (V.scale (sigma k))),
              ((F (sigma k)).connection (t (sigma k))).scalarCurvature z ≤
                (2 * ((m : ℝ) + 1)) * V.scale (sigma k)) →
          TerminalCommonIntervalSlab (terminalCommonInterval_reindex V sigma hsigma)
            (duration m / 2)) ∧
        ∀ (sigma : ℕ → ℕ), StrictMono sigma → ∀ j : ℕ, ∀ᶠ k in atTop,
          ∀ (C : GeneralizedSliceCarrier.{u}) {U : Set C.carrier}, IsOpen U →
          ∀ {a : ℝ} (ha : a ∈ Ico (-((j : ℝ) + 1)) 0),
          ∀ E : SurgeryFlowCylinder (F (sigma k)) C (t (sigma k))
              (V.scale (sigma k)) (Icc a 0) U,
            (∀ s (hs : s ∈ Icc a 0), ∀ x ∈ U,
              ((F (sigma k)).connection (t (sigma k) + s / V.scale (sigma k))).scalarCurvature
                (E.forward s hs x) ≤ ((j : ℝ) + 1) * V.scale (sigma k)) →
            let bottom : a ∈ Icc a 0 := ⟨le_rfl, ha.2.le⟩
            let zero : (0 : ℝ) ∈ Icc a 0 := ⟨ha.2.le, le_rfl⟩
            let tbirth := t (sigma k) + a / V.scale (sigma k)
            ∀ (hEvent : tbirth ∈ (F (sigma k)).surgery_times),
            ∀ [Nonempty ((F (sigma k)).slice tbirth).carrier],
            ∀ (i : Fin ((F (sigma k)).event tbirth hEvent).cap_count) (contact : C.carrier),
              contact ∈ U →
              E.forward a bottom contact ∈ (((F (sigma k)).event tbirth hEvent).caps i).carrier →
              (∀ x ∈ U, ((F (sigma k)).metric tbirth).edist
                (E.forward a bottom contact) (E.forward a bottom x) ≤
                  ENNReal.ofReal (((j : ℝ) + 1) / Real.sqrt (V.scale (sigma k)))) →
              ∀ y ∈ U,
                ((F (sigma k)).connection (t (sigma k) + 0 / V.scale (sigma k))).scalarCurvature
                  (E.forward 0 zero y) = V.scale (sigma k) →
                SurgeryCanonicalControl (F (sigma k)) (t (sigma k) + 0 / V.scale (sigma k))
                  (E.forward 0 zero y) (F (sigma k)).parameters.epsilon
                  (F (sigma k)).parameters.C := by
  classical
  choose Qcap hQcap _hQcapScale factory using fun j : ℕ =>
    exists_finite_source_cap_canonical_cutoff P S B p hp
      (T := (j : ℝ) + 1) (K := (j : ℝ) + 1) (D := (j : ℝ) + 1)
      (by positivity) (by positivity) (by positivity)
  let r0 : ℕ → ℝ := fun n => p.r (Fin.last p.i) / ((n : ℝ) + 1)
  have hr0 (n : ℕ) : 0 < r0 n ∧ r0 n ≤ p.r (Fin.last p.i) :=
    Proofs.M47.canonicalInduction_radius_bounds (p.r_pos _) n
  choose dcap hdcap _hdcapLast applyCap using fun j n =>
    factory j (r0 n) (hr0 n).1 (hr0 n).2
  obtain ⟨kappa, hkappa, tau, K, duration, hsourceConstants, hDuration, sequence⟩ :=
    terminalSource_exists_regular_sequence_common_budget P S B N p hp A hA
      (fun _ htheta _ hv z =>
        exists_source_standard_canonical_neighborhood P S B p hp htheta hv z) hno
  refine ⟨kappa, hkappa, tau, K, duration, hsourceConstants, hDuration, ?_⟩
  intro c hc
  let stages (n : ℕ) := Finset.range (n + 1)
  have hstages (n : ℕ) : (stages n).Nonempty := ⟨0, by simp [stages]⟩
  let cutoff : ℕ → ℝ := fun n =>
    min (c n) ((stages n).inf' (hstages n) (fun j => dcap j n))
  have hcutoff (n : ℕ) : 0 < cutoff n := by
    apply lt_min (hc n)
    exact (Finset.lt_inf'_iff (hstages n)).mpr (fun j _ => hdcap j n)
  have hcutStage (n j : ℕ) (hj : j ≤ n) : cutoff n ≤ dcap j n := by
    exact (min_le_right _ _).trans (Finset.inf'_le (fun j => dcap j n)
      (show j ∈ stages n from Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))
  obtain ⟨n0, r, delta, F, O, t, W, H, ht, y, hPositive, hDiverges,
    hrLimit, hdLimit, data, volume, source, common⟩ := sequence cutoff hcutoff
  let V := regularHistoryBlowupSequence F W H t ht y hPositive hDiverges
  have hscale (n : ℕ) : ((F n).connection (t n)).scalarCurvature
      ((H n).history.forward (t n) (ht n) (y n)) = V.scale n :=
    (H n).scalar_pullback (t n) (ht n) (y n)
  refine ⟨n0, r, delta, F, O, t, W, H, ht, y, hPositive, hDiverges,
    hrLimit, hdLimit, ?_, volume, source, common, ?_⟩
  · intro n
    rcases data n with ⟨hrEq, hW, hr, hrLast, hdelta, hcut, hN,
      hnext, old, hadmissible, hpinch, hpolicy, scales, overlap,
      hbase, hinf, past, high, bad, vol⟩
    exact ⟨hrEq, hW, hr, hrLast, hdelta, hcut.trans (min_le_left _ _), hN,
      hnext, old, hadmissible, hpinch, hpolicy, scales, overlap,
      hbase, hinf, past, high, bad, vol⟩
  · intro sigma hsigma j
    have hdiverges := V.scalar_diverges.comp hsigma.tendsto_atTop
    filter_upwards [hdiverges.eventually (eventually_ge_atTop (Qcap j)),
      hsigma.tendsto_atTop.eventually (eventually_ge_atTop j)] with k hLarge hIndex
    rcases data (sigma k) with ⟨hrEq, _hW, _hr, _hrLast, _hdelta, hcut, _hN,
      hnext, old, hadmissible, hpinch, _hpolicy, scales, overlap,
      hbase, _hinf, past, high, _bad, _vol⟩
    have hrEq' : r (sigma k) = r0 (sigma k + n0) := hrEq
    have hdj : delta (sigma k) ≤ dcap j (sigma k + n0) :=
      hcut.trans (hcutStage (sigma k + n0) j (hIndex.trans (Nat.le_add_right _ _)))
    have hpost : SurgeryPostPrefixScales p (F (sigma k)) (O (sigma k))
        (r0 (sigma k + n0)) (dcap j (sigma k + n0)) := by
      rw [← hrEq']
      exact scales.mono_delta hdj
    have hfloor : (r0 (sigma k + n0))⁻¹ ^ 2 ≤ V.scale (sigma k) := by
      simpa only [← hrEq', ← hscale (sigma k)] using high
    have hPast : SurgeryCanonicalOn (F (sigma k))
        (surgeryObservationInterval (O (sigma k)) ∩ Iio (t (sigma k)))
        (r0 (sigma k + n0)) := by
      rw [← hrEq']
      exact fun s hs hsF z hz => past s ⟨hs.1.1, hs.2⟩ hsF z hz
    exact applyCap j (sigma k + n0) (F (sigma k)) (O (sigma k)) hnext.2 old
      hadmissible hpinch hpost
      (fun s hs => (overlap s ⟨hs.1, hs.2.1, hs.1.2⟩).trans hdj)
      hbase hLarge hfloor hPast

end PoincareConjecture.M47
