import PoincareConjecture.Proofs.M47.TerminalRegularSequenceSources
import PoincareConjecture.Proofs.M47.TerminalUniformSourceCylinder
import PoincareConjecture.Proofs.M47.TerminalCommonIntervalAssembly
import PoincareConjecture.Proofs.M47.TerminalCommonIntervalSlabs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology

universe u

namespace PoincareConjecture.M47

theorem terminalSource_exists_regular_sequence_common_budget
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (N : RepairedNoncollapseInductionData S)
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    (A : ℕ → ℝ) (hA : ∀ j, 0 < A j)
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
        ∀ (sigma : ℕ → ℕ) (hsigma : StrictMono sigma) (m : ℕ),
          (∀ a : ℝ, 0 < a → ∀ᶠ k in atTop,
            ∀ z ∈ ((F (sigma k)).metric (t (sigma k))).ball
                ((H (sigma k)).history.forward (t (sigma k)) (ht (sigma k)) (y (sigma k)))
                (a / Real.sqrt (V.scale (sigma k))),
              ((F (sigma k)).connection (t (sigma k))).scalarCurvature z ≤
                (2 * ((m : ℝ) + 1)) * V.scale (sigma k)) →
          TerminalCommonIntervalSlab (terminalCommonInterval_reindex V sigma hsigma)
            (duration m / 2) := by
  classical
  choose duration hDuration hDurationOne uniform using fun m : ℕ =>
    exists_first_failure_uniform_source_cylinder_of_pointwise P.toM46 S B p hp
      pointwise (K := (m : ℝ) + 1) (le_add_of_nonneg_left (Nat.cast_nonneg m))
  choose Q0 hQ0 factory using fun m j : ℕ =>
    uniform m ((j : ℝ) + 1) (by positivity)
  let r0 : ℕ → ℝ := fun n => p.r (Fin.last p.i) / ((n : ℝ) + 1)
  have hr0 (n : ℕ) : 0 < r0 n ∧ r0 n ≤ p.r (Fin.last p.i) :=
    Proofs.M47.canonicalInduction_radius_bounds (p.r_pos _) n
  choose d hd _hdLast applyCylinder using fun m j n =>
    factory m j (r0 n) (hr0 n).1 (hr0 n).2
  obtain ⟨kappa, hkappa, tau, K, hsourceConstants, sequence⟩ :=
    terminalSource_exists_regular_sequence_sources P S B N p hp A hA pointwise hno
  refine ⟨kappa, hkappa, tau, K, duration, hsourceConstants,
    fun m => ⟨hDuration m, hDurationOne m⟩, ?_⟩
  intro c hc
  let stages (n : ℕ) := (Finset.range (n + 1)).product (Finset.range (n + 1))
  have hstages (n : ℕ) : (stages n).Nonempty := ⟨(0, 0), by simp [stages]⟩
  let cutoff : ℕ → ℝ := fun n =>
    min (c n) ((stages n).inf' (hstages n) (fun ij => d ij.1 ij.2 n))
  have hcutoff (n : ℕ) : 0 < cutoff n := by
    apply lt_min (hc n)
    exact (Finset.lt_inf'_iff (hstages n)).mpr (fun ij _ => hd ij.1 ij.2 n)
  have hcutStage (n m j : ℕ) (hm : m ≤ n) (hj : j ≤ n) : cutoff n ≤ d m j n := by
    exact (min_le_right _ _).trans (Finset.inf'_le (fun ij => d ij.1 ij.2 n)
      (show (m, j) ∈ stages n from Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hm),
          Finset.mem_range.mpr (Nat.lt_succ_of_le hj)⟩))
  obtain ⟨n0, r, delta, F, O, t, W, H, ht, y, hPositive, hDiverges,
    hrLimit, hdLimit, data, volume, sourceSigma, hSourceSigma, hsource⟩ :=
      sequence cutoff hcutoff
  let V := regularHistoryBlowupSequence F W H t ht y hPositive hDiverges
  have hscale (n : ℕ) : ((F n).connection (t n)).scalarCurvature
      ((H n).history.forward (t n) (ht n) (y n)) = V.scale n :=
    (H n).scalar_pullback (t n) (ht n) (y n)
  refine ⟨n0, r, delta, F, O, t, W, H, ht, y, hPositive, hDiverges,
    hrLimit, hdLimit, ?_, volume, ⟨sourceSigma, hSourceSigma, hsource⟩, ?_⟩
  · intro n
    rcases data n with ⟨hrEq, hW, hr, hrLast, hdelta, hcut, hN,
      hnext, old, hadmissible, hpinch, hpolicy, scales, overlap,
      hbase, hinf, past, high, bad, vol⟩
    exact ⟨hrEq, hW, hr, hrLast, hdelta, hcut.trans (min_le_left _ _), hN,
      hnext, old, hadmissible, hpinch, hpolicy, scales, overlap,
      hbase, hinf, past, high, bad, vol⟩
  · intro sigma hsigma m hterminal
    refine ⟨13 * max (8 * ((m : ℝ) + 1)) 1, by positivity, fun a ha eta heta => ?_⟩
    obtain ⟨j, hj⟩ := exists_nat_ge a
    have haj : a ≤ (j : ℝ) + 1 := by linarith only [hj]
    have hAj : 0 < (j : ℝ) + 1 := by positivity
    have hdiverges := V.scalar_diverges.comp hsigma.tendsto_atTop
    filter_upwards [hterminal ((j : ℝ) + 1) hAj,
      hdiverges.eventually (eventually_ge_atTop (Q0 m j)),
      hdiverges.eventually (eventually_ge_atTop (blowupPinchingThreshold
        (8 * ((m : ℝ) + 1)) eta)),
      hsigma.tendsto_atTop.eventually (eventually_ge_atTop (max m j))]
      with k hTerminal hLarge hPinching hIndex
    rcases data (sigma k) with ⟨hrEq, _hW, _hr, _hrLast, _hdelta, hcut, _hN,
      hnext, old, hadmissible, hpinch, _hpolicy, scales, overlap,
      hbase, _hinf, past, high, bad, _vol⟩
    have hrEq' : r (sigma k) = r0 (sigma k + n0) := hrEq
    have hdj : delta (sigma k) ≤ d m j (sigma k + n0) :=
      hcut.trans (hcutStage (sigma k + n0) m j
        (((le_max_left m j).trans hIndex).trans (Nat.le_add_right _ _))
        (((le_max_right m j).trans hIndex).trans (Nat.le_add_right _ _)))
    have hpost : SurgeryPostPrefixScales p (F (sigma k)) (O (sigma k))
        (r0 (sigma k + n0)) (d m j (sigma k + n0)) := by
      rw [← hrEq']
      exact scales.mono_delta hdj
    have hfloor : (r0 (sigma k + n0))⁻¹ ^ 2 ≤ V.scale (sigma k) := by
      simpa only [← hrEq', ← hscale (sigma k)] using high
    have hPast : SurgeryCanonicalOn (F (sigma k))
        (surgeryObservationInterval (O (sigma k)) ∩ Iio (t (sigma k)))
        (r0 (sigma k + n0)) := by
      rw [← hrEq']
      exact fun s hs hsF z hz => past s ⟨hs.1.1, hs.2⟩ hsF z hz
    obtain ⟨e, he, hb⟩ := applyCylinder m j (sigma k + n0) (F (sigma k))
      (O (sigma k)) hnext.2 old hadmissible hpinch hpost
      (fun s hs => (overlap s ⟨hs.1, hs.2.1, hs.1.2⟩).trans hdj)
      (W (sigma k)) (H (sigma k)) (ht (sigma k)) hbase hLarge hfloor hPast
      (y (sigma k)) rfl bad eta heta hPinching hTerminal
    obtain ⟨controlled⟩ := terminalCommonInterval_controlled_of_long_search
      F W H t ht y hPositive hDiverges (sigma k) hAj (half_pos (hDuration m))
      (by linarith only [hDuration m] : -(duration m) < -(duration m / 2))
      e he (fun s hs z hz => (hb s hs z hz).1) (fun s hs z hz => (hb s hs z hz).2)
    exact ⟨terminalCommonInterval_reindexCylinder hsigma
      (terminalCommonInterval_restrict controlled haj le_rfl le_rfl le_rfl)⟩

end PoincareConjecture.M47
