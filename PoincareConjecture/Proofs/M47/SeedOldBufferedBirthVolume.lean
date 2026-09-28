import PoincareConjecture.Proofs.M47.SeedPastSearchVolume
import PoincareConjecture.Proofs.M47.SeedOldBufferedWindow
import PoincareConjecture.Proofs.M47.SeedOrdinaryGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

theorem exists_seed_old_buffered_ordinary_birth_volume
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    {A alpha B : ℝ} (hA : 1 ≤ A) (halpha : 0 < alpha) (hB : 1 ≤ B) :
    ∃ V : ℝ, 0 < V ∧ ∀ rNext : ℝ, 0 < rNext → rNext ≤ p.r (Fin.last p.i) →
      ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
        ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
          surgeryEpochStart p.i < O.H → O.H ≤ surgeryEpochStart (p.i + 1) →
          SurgeryPrefixControls p F O → SurgeryFlowAdmissible F → SurgeryFlowPinched F →
          SurgeryFlowTerminalPolicyOn F (surgeryObservationInterval O) →
          SurgeryPostPrefixScales p F O rNext cutoff →
          (∀ t ∈ surgeryObservationInterval O ∩ overlapInterval p,
            F.parameters.delta t ≤ cutoff) →
        ∀ (C : GeneralizedSliceCarrier.{u}) (origin scale : ℝ) (I : Set ℝ)
          (U : TopologicalSpace.Opens C.carrier), IsCompact (U : Set C.carrier) →
        ∀ (e : SurgeryFlowCylinder F C origin scale I U) (s : ℝ) (hs : s ∈ I),
        ∀ d : ℝ, 0 < d → d ≤ (p.r (Fin.last p.i)) ^ 2 / (32 * A) →
          origin + s / scale + d ∈
            Icc (surgeryEpochStart p.i - 1 / 128) (surgeryEpochStart p.i) →
        ∀ (g : RiemannianMetric 3 U) (D : LeviCivitaData g),
          (∀ y : U, ∀ v w : TangentSpace (𝓡 3) y,
            g.inner y v w = (F.metric (origin + s / scale)).inner (e.forward s hs y.val)
              (mfderiv (𝓡 3) (𝓡 3) (fun z : U => e.forward s hs z.val) y v)
              (mfderiv (𝓡 3) (𝓡 3) (fun z : U => e.forward s hs z.val) y w)) →
          (∀ y : U, D.scalarCurvature y =
            (F.connection (origin + s / scale)).scalarCurvature (e.forward s hs y.val)) →
        ∀ q : U,
          (∀ y ∈ g.ball q (Real.sqrt (alpha * d) / (4 * A)),
            D.scalarCurvature y ≤ 4 * B / d) →
          (¬ SurgeryPositiveComponentAt F (origin + s / scale) (e.forward s hs q.val) ∨
            ∃ hT : origin + s / scale ∈ F.surgery_times,
              ∀ [Nonempty (F.slice (origin + s / scale)).carrier],
                ∃ i : Fin (F.event (origin + s / scale) hT).cap_count,
                  (connectedComponent (e.forward s hs q.val) ∩
                    ((F.event (origin + s / scale) hT).caps i).carrier).Nonempty) →
          ENNReal.ofReal (V * Real.sqrt d ^ 3) ≤
            calibratedMetricVolume g (g.ball q ((Real.sqrt (alpha * d) / (4 * A)) / 2)) := by
  obtain ⟨k, hk, volume⟩ := exists_seed_past_search_volume P S p hp
  obtain ⟨Bsearch, sigma, lambda, hBsearch, _hBsearchOne, hsigma, hlambda,
      _hlambdaSmall, searchScales⟩ := exists_seed_observed_search_scales S p
  obtain ⟨M, hM, _hMone, _hMB, birthScales⟩ :=
    exists_seed_young_birth_scale hA halpha hB hlambda
  let V := k * lambda ^ 3 / (64 * Real.sqrt M ^ 3)
  have hV : 0 < V := by dsimp only [V]; positivity
  let rho := p.r (Fin.last p.i)
  have hrho : 0 < rho := p.r_pos _
  have hApos : 0 < A := zero_lt_one.trans_le hA
  refine ⟨V, hV, ?_⟩
  intro rNext hrNext hrLast
  obtain ⟨cutoff, hcutoff, hcutoffLast, search⟩ := volume rNext hrNext hrLast
  refine ⟨cutoff, hcutoff, hcutoffLast, ?_⟩
  intro F O hEnd hHorizon old admissible pinched policy scales overlap
    C origin scale I U hcompact e s hs d hd hyoung hfuture g D hmetric hread q hscalar hbirth
  let : CompactSpace U := isCompact_iff_compactSpace.mp hcompact
  let H := M / d
  let r := lambda / Real.sqrt H
  let R := Real.sqrt (alpha * d) / (4 * A)
  have hR : 0 < R := by dsimp only [R]; positivity
  obtain ⟨hH, hlevel, hr, hrR, hscalarScale, hrUnits⟩ :=
    birthScales d rho hd hrho hyoung
  obtain ⟨hduration, _hr, hroot, hscalarTime, hmetricTime, hrepsilon,
      hbudget, hrd, htest, _hrho, hdOld⟩ := searchScales rho hrho le_rfl H hH hlevel
  have hyoung32 : d ≤ rho ^ 2 / 32 := by
    have h := (le_div_iff₀ (by positivity : 0 < 32 * A)).mp hyoung
    nlinarith only [h, hA, hd]
  have hwindow : Icc (origin + s / scale - sigma / H) (origin + s / scale) ⊆
      surgeryObservationInterval O ∩ Ici (surgeryEpochStart (p.i - 1)) := by
    simpa only [add_sub_cancel_right] using
      seed_old_buffered_birth_search_window p hEnd hfuture hd.le hyoung32 hdOld
  have hEndPos : 0 < surgeryEpochStart p.i := by unfold surgeryEpochStart; positivity
  let short := O.restrictTo (surgeryEpochStart p.i) hEndPos hEnd.le
  have hshort : short.H ≤ O.H := hEnd.le
  have hshortWindow : Icc (origin + s / scale - sigma / H) (origin + s / scale) ⊆
      surgeryObservationInterval short ∩ Ici (surgeryEpochStart (p.i - 1)) := by
    intro t ht
    exact ⟨⟨(hwindow ht).1.1, by
      change t < surgeryEpochStart p.i
      linarith only [ht.2, hfuture.2, hd]⟩, (hwindow ht).2⟩
  have hcanonical : SurgeryCanonicalOn F (surgeryObservationInterval short) rNext :=
    (old.canonicalOn_prefixFinal hrNext hrLast).restrict (fun t ht =>
      ⟨SurgeryObservation.interval_subset_of_horizon_le hshort ht, ht⟩)
  have hphysical := seed_ordinary_scalar_ball_bound U e s hs g D hmetric hread q hR hscalar
  have hphysicalSmall : ∀ y ∈ (F.metric (origin + s / scale)).ball (e.forward s hs q.val) r,
      (F.connection (origin + s / scale)).scalarCurvature y ≤ 2 * H := by
    intro y hy
    exact (hphysical y (hy.trans_le (ENNReal.ofReal_le_ofReal hrR))).trans hscalarScale
  have hv := search H Bsearch (sigma / H) r hH hBsearch hduration hr hlevel
    hroot hscalarTime hmetricTime hrepsilon hbudget hrd htest F short
    (hshort.trans hHorizon) (old.restrictObservation hshort) admissible pinched
    (policy.restrictObservation hshort) (scales.restrictObservation hshort) hcanonical
    (fun t ht => overlap t ⟨SurgeryObservation.interval_subset_of_horizon_le hshort ht.1, ht.2⟩)
    (origin + s / scale) (by linarith only [hfuture.2, hd]) hshortWindow
    (e.forward s hs q.val) hphysicalSmall hbirth
  have hvOrdinary := seed_ordinary_birth_volume U e s hs g hmetric q hr hv
  have hunits : k * (r / 2) ^ 3 / 8 = V * Real.sqrt d ^ 3 := by
    dsimp only [r, H]
    rw [hrUnits]
    dsimp only [V]
    ring
  rw [hunits] at hvOrdinary
  exact hvOrdinary.trans (measure_mono (fun y hy =>
    hy.trans_le (ENNReal.ofReal_le_ofReal hrR)))

end PoincareConjecture.Proofs.M47
