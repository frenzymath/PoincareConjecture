import PoincareConjecture.Proofs.M47.SeedRegularSequence
import PoincareConjecture.Proofs.M07.Topology.Sequences.Diagonal










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology

universe u

namespace PoincareConjecture.M47




theorem terminalSource_exists_regular_sequence_sources
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
    ∃ kappa : ℝ, 0 < kappa ∧ ∃ tau K : ℕ → ℝ,
      (∀ j, 0 < tau j ∧ tau j ≤ 1 ∧ 0 < K j) ∧
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
        ∃ sigma : ℕ → ℕ, StrictMono sigma ∧ ∀ k j, j ≤ k →
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
                (e.forward s hs z) ≤ K j * V.scale (sigma k) := by
  classical
  choose Q0 tau K hQ0 htau htauOne hK factory using fun j =>
    exists_first_failure_source_cylinder_of_pointwise P.toM46 S B p hp (hA j) pointwise
  obtain ⟨kappa, hkappa, sequence⟩ :=
    Proofs.M47.exists_seed_regular_counterexample_sequence_of_pointwise P S B N p hp pointwise hno
  let r0 : ℕ → ℝ := fun n => p.r (Fin.last p.i) / ((n : ℝ) + 1)
  have hr0 (n : ℕ) : 0 < r0 n ∧ r0 n ≤ p.r (Fin.last p.i) :=
    Proofs.M47.canonicalInduction_radius_bounds (p.r_pos _) n
  choose d hd _hdLast applyCylinder using fun j n =>
    factory j (r0 n) (hr0 n).1 (hr0 n).2
  refine ⟨kappa, hkappa, tau, K, fun j => ⟨htau j, htauOne j, hK j⟩, ?_⟩
  intro c hc
  let stages (n : ℕ) := Finset.range (n + 1)
  have hstages (n : ℕ) : (stages n).Nonempty := ⟨0, by simp [stages]⟩
  let cutoff : ℕ → ℝ := fun n => min (c n) ((stages n).inf' (hstages n) (fun j => d j n))
  have hcutoff (n : ℕ) : 0 < cutoff n := by
    apply lt_min (hc n)
    exact (Finset.lt_inf'_iff (hstages n)).mpr (fun j _ => hd j n)
  have hcutStage (n j : ℕ) (hj : j ≤ n) : cutoff n ≤ d j n := by
    exact (min_le_right _ _).trans (Finset.inf'_le (fun j => d j n)
      (show j ∈ stages n from Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))
  obtain ⟨n0, r, delta, F, O, t, W, H, ht, y, hPositive, hDiverges,
    hrLimit, hdLimit, data, volume⟩ := sequence cutoff hcutoff
  let V := regularHistoryBlowupSequence F W H t ht y hPositive hDiverges
  have hscale (n : ℕ) : ((F n).connection (t n)).scalarCurvature
      ((H n).history.forward (t n) (ht n) (y n)) = V.scale n :=
    (H n).scalar_pullback (t n) (ht n) (y n)
  have hstage (j : ℕ) : ∀ᶠ n in atTop,
      ∃ e : SurgeryFlowCylinder (F n) ((F n).slice (t n)) (t n) (V.scale n)
          (Icc (-(tau j)) 0) (((F n).metric (t n)).ball
            ((H n).history.forward (t n) (ht n) (y n)) (A j / Real.sqrt (V.scale n))),
        (∀ hs z, z ∈ ((F n).metric (t n)).ball
            ((H n).history.forward (t n) (ht n) (y n)) (A j / Real.sqrt (V.scale n)) →
          HEq (e.forward 0 hs z) z) ∧
        ∀ s hs z, z ∈ ((F n).metric (t n)).ball
            ((H n).history.forward (t n) (ht n) (y n)) (A j / Real.sqrt (V.scale n)) →
          ((F n).connection (t n + s / V.scale n)).curvatureTensorNorm
            (e.forward s hs z) ≤ K j * V.scale n := by
    have hlarge : ∀ᶠ n in atTop, Q0 j ≤ V.scale n :=
      V.scalar_diverges.eventually (eventually_ge_atTop (Q0 j))
    filter_upwards [hlarge, eventually_ge_atTop j] with n hlarge hjn
    rcases data n with ⟨hrEq, _hW, _hr, _hrLast, _hd, hcut, _hN,
      hnext, old, hadmissible, hpinch, _hpolicy, scales, overlap,
      hbase, _hinf, past, high, bad, _vol⟩
    have hrEq' : r n = r0 (n + n0) := hrEq
    have hdj : delta n ≤ d j (n + n0) :=
      hcut.trans (hcutStage (n + n0) j (hjn.trans (Nat.le_add_right n n0)))
    apply applyCylinder j (n + n0) (F n) (O n) hnext.2 old hadmissible hpinch
      (by rw [← hrEq']; exact scales.mono_delta hdj)
      (fun s hs => (overlap s ⟨hs.1, hs.2.1, hs.1.2⟩).trans hdj)
      (W n) (H n) (ht n) hbase hlarge
    · simpa only [← hrEq', ← hscale n] using high
    · rw [← hrEq']
      exact fun s hs hsF z hz => past s ⟨hs.1.1, hs.2⟩ hsF z hz
    · exact rfl
    · exact bad
  obtain ⟨sigma, hsigma, hselect⟩ := Poincare.exists_strictMono_forall_le_of_eventually hstage
  refine ⟨n0, r, delta, F, O, t, W, H, ht, y, hPositive, hDiverges,
    hrLimit, hdLimit, ?_, volume, sigma, hsigma, hselect⟩
  intro n
  rcases data n with ⟨hrEq, hW, hr, hrLast, hd, hcut, hN,
    hnext, old, hadmissible, hpinch, hpolicy, scales, overlap,
    hbase, hinf, past, high, bad, vol⟩
  exact ⟨hrEq, hW, hr, hrLast, hd, hcut.trans (min_le_left _ _), hN,
    hnext, old, hadmissible, hpinch, hpolicy, scales, overlap,
    hbase, hinf, past, high, bad, vol⟩

end PoincareConjecture.M47
