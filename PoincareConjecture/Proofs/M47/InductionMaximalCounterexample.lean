import PoincareConjecture.Proofs.M47.TerminalRegularFiniteCapBudget
import PoincareConjecture.Proofs.M47.TerminalRegularRetainedCeiling
import PoincareConjecture.Proofs.M47.TerminalRegularCommonApplication

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ENNReal

universe u

namespace PoincareConjecture.M47

theorem exists_maximal_regular_counterexample
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (N : RepairedNoncollapseInductionData S)
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    (hno : ¬ Nonempty (SurgeryCanonicalExtension p (Classical.choice (N.induction p hp)))) :
    ∃ kappa : ℝ, 0 < kappa ∧
      ∃ (r : ℕ → ℝ) (F : ℕ → SurgeryFlowData.{u}) (O : ∀ n, SurgeryObservation (F n))
        (t : ℕ → ℝ) (W : ∀ n, M33RegularHistoryWindow (F n))
        (history : ∀ n, M33RegularHistoryData (W n))
        (ht : ∀ n, t n ∈ (history n).generalized.interval)
        (x : ∀ n, ((history n).generalized.slice (t n)).carrier),
      ∃ (hPositive : ∀ n, 0 < ((F n).connection (t n)).scalarCurvature
          ((history n).history.forward (t n) (ht n) (x n)))
        (hDiverges : Tendsto (fun n => ((F n).connection (t n)).scalarCurvature
          ((history n).history.forward (t n) (ht n) (x n))) atTop atTop),
      let V := regularHistoryBlowupSequence F W history t ht x hPositive hDiverges
      (∀ n, SurgeryPrefixControls p (F n) (O n) ∧
        t n ∈ Ico (surgeryEpochStart p.i) (O n).H ∧
        SurgeryFlowPinched (F n) ∧
        SurgeryCanonicalOn (F n) (Ico 0 (t n)) (r n) ∧
        (r n)⁻¹ ^ 2 ≤ V.scale n ∧
        ¬ SurgeryCanonicalControl (F n) (t n)
          ((history n).history.forward (t n) (ht n) (x n))
          (F n).parameters.epsilon (F n).parameters.C ∧
        SurgeryVolumeControlOn (F n) (Icc (surgeryEpochStart p.i - 1 / 128) (t n)) kappa
          (fun _ _ => True) ∧
        ∀ s ∈ surgeryObservationInterval (O n) ∩
          Ico (surgeryEpochStart (p.i - 1)) (O n).H,
            (F n).parameters.delta s ≤ B.delta S.setup.standard_initial S.constants) ∧
      (∀ (sigma : ℕ → ℕ), StrictMono sigma → ∀ j : ℕ, ∀ᶠ k in atTop,
        ∀ (C : GeneralizedSliceCarrier.{u}) {U : Set C.carrier}, IsOpen U →
        ∀ {a : ℝ} (ha : a ∈ Ico (-((j : ℝ) + 1)) 0),
        ∀ E : SurgeryFlowCylinder (F (sigma k)) C (t (sigma k))
            (V.scale (sigma k)) (Icc a 0) U,
          (∀ s (hs : s ∈ Icc a 0), ∀ z ∈ U,
            ((F (sigma k)).connection (t (sigma k) + s / V.scale (sigma k))).scalarCurvature
              (E.forward s hs z) ≤ ((j : ℝ) + 1) * V.scale (sigma k)) →
          let bottom : a ∈ Icc a 0 := ⟨le_rfl, ha.2.le⟩
          let zero : (0 : ℝ) ∈ Icc a 0 := ⟨ha.2.le, le_rfl⟩
          let tbirth := t (sigma k) + a / V.scale (sigma k)
          ∀ (hEvent : tbirth ∈ (F (sigma k)).surgery_times),
          ∀ [Nonempty ((F (sigma k)).slice tbirth).carrier],
          ∀ (i : Fin ((F (sigma k)).event tbirth hEvent).cap_count) (contact : C.carrier),
            contact ∈ U →
            E.forward a bottom contact ∈ (((F (sigma k)).event tbirth hEvent).caps i).carrier →
            (∀ z ∈ U, ((F (sigma k)).metric tbirth).edist
              (E.forward a bottom contact) (E.forward a bottom z) ≤
                ENNReal.ofReal (((j : ℝ) + 1) / Real.sqrt (V.scale (sigma k)))) →
            ∀ y ∈ U,
              ((F (sigma k)).connection (t (sigma k) + 0 / V.scale (sigma k))).scalarCurvature
                (E.forward 0 zero y) = V.scale (sigma k) →
              SurgeryCanonicalControl (F (sigma k)) (t (sigma k) + 0 / V.scale (sigma k))
                (E.forward 0 zero y) (F (sigma k)).parameters.epsilon
                (F (sigma k)).parameters.C) ∧
      ∃ (rho : ℕ → ℕ) (hrho : StrictMono rho),
        let D := terminalCommonInterval_reindex V rho hrho
        TerminalCommonIntervalDecided D ∧
          M30GeometricLongControls D (terminalCommonIntervalHorizon D) ∧
          Nonempty (GeneralizedBlowupConvergence D
            (blowupBackwardInterval (terminalCommonIntervalHorizon D))) := by
  classical
  let A : ℕ → ℝ := fun j => (j : ℝ) + 1
  have hA : ∀ j, 0 < A j := fun j => by dsimp [A]; positivity
  obtain ⟨kappa, hkappa, tau, K, duration, hsourceConstants, hDuration, sequence⟩ :=
    terminalSource_exists_regular_sequence_finite_cap_budget P S B N p hp A hA hno
  obtain ⟨n0, r, delta, F, O, t, W, history, ht, x, hPositive, hDiverges,
    _hrlim, hdlim, hdata, volume, ⟨alpha, halpha, sources⟩, budget, capBudget⟩ :=
    sequence (fun _ => B.delta S.setup.standard_initial S.constants)
      (fun _ => B.delta_pos _ _)
  let V := regularHistoryBlowupSequence F W history t ht x hPositive hDiverges
  have core (n : ℕ) :
      SurgeryPrefixControls p (F n) (O n) ∧
      t n ∈ Ico (surgeryEpochStart p.i) (O n).H ∧
      SurgeryFlowPinched (F n) ∧
      SurgeryCanonicalOn (F n) (Ico 0 (t n)) (r n) ∧
      (r n)⁻¹ ^ 2 ≤ ((F n).connection (t n)).scalarCurvature
        ((history n).history.forward (t n) (ht n) (x n)) ∧
      ¬ SurgeryCanonicalControl (F n) (t n)
        ((history n).history.forward (t n) (ht n) (x n))
        (F n).parameters.epsilon (F n).parameters.C ∧
      SurgeryVolumeControlOn (F n) (Icc (surgeryEpochStart p.i - 1 / 128) (t n)) kappa
        (fun _ _ => True) ∧
      (∀ s ∈ surgeryObservationInterval (O n) ∩
        Ico (surgeryEpochStart (p.i - 1)) (O n).H, (F n).parameters.delta s ≤ delta n) ∧
      delta n ≤ B.delta S.setup.standard_initial S.constants := by
    obtain ⟨_hrEq, _hwindow, _hrpos, _hrLast, _hdpos, hdc, _hdcut, _hobs,
      old, _hadm, hpin, _hpol, _hscale, hover, hbase, _hfirst, hpast, hfloor,
      hbad, hvol⟩ := hdata n
    exact ⟨old, hbase, hpin, hpast, hfloor, hbad, hvol, hover, hdc⟩
  choose old hBase hPinched hPast hFloor hbad hvolume hOverlap hdelta using core
  obtain ⟨rvol, vvol, hrvol, hvvol, terminalVolume⟩ := volume
  have hcofinal (a : ℝ) (_ha : 0 < a) : ∃ j, a ≤ A j := by
    obtain ⟨j, hj⟩ := exists_nat_ge a
    exact ⟨j, by dsimp [A]; linarith⟩
  obtain ⟨xi, hxi, K0, _hK0, ceiling, compactBalls⟩ :=
    terminalSource_regular_retained_ceiling P S B p hp F O W history t r delta ht x
      old hBase hPinched hPast hFloor hOverlap hdlim hDiverges A tau K hA
      (fun j => (hsourceConstants j).1) (fun j => (hsourceConstants j).2.2.le)
      hcofinal hrvol hvvol terminalVolume alpha halpha sources
  let nu := alpha ∘ xi
  have hnu : StrictMono nu := halpha.comp hxi
  obtain ⟨delta0, hdelta0, initialSlab⟩ :=
    terminalSource_common_slab_of_physical_ceiling F W history t ht x hPositive hDiverges
      duration (fun m => (hDuration m).1) nu hnu K0 budget ceiling
  have hcompact : BlowupBaseBallsCompact (terminalCommonInterval_reindex V nu hnu) :=
    compactBalls
  have hvol : ∃ rho v : ℝ, 0 < rho ∧ 0 < v ∧ ∀ᶠ k in atTop,
      ENNReal.ofReal (v / (Real.sqrt (V.scale (nu k))) ^ 3) ≤
        calibratedMetricVolume ((V.flow (nu k)).metric (V.base (nu k)).1)
          (V.baseBall (nu k) rho) :=
    ⟨rvol, vvol, hrvol, hvvol, hnu.tendsto_atTop.eventually terminalVolume⟩
  obtain ⟨lambda, hlambda, hdec, controls, _hmaximal, convergence⟩ :=
    terminalSource_common_maximal_selected_limit P
      (terminalCommonInterval_reindex V nu hnu) hdelta0 initialSlab hcompact hvol
  refine ⟨kappa, hkappa, r, F, O, t, W, history, ht, x, hPositive, hDiverges,
    ?_, capBudget, nu ∘ lambda, hnu.comp hlambda, hdec, controls, convergence⟩
  intro n
  refine ⟨old n, hBase n, hPinched n, hPast n, ?_, hbad n, hvolume n, ?_⟩
  · exact (hFloor n).trans_eq ((history n).scalar_pullback (t n) (ht n) (x n))
  · intro s hs
    exact (hOverlap n s hs).trans (hdelta n)

end PoincareConjecture.M47
