import PoincareConjecture.Proofs.M47.SeedYoungBirthScales
import PoincareConjecture.Proofs.M47.SeedOrdinaryGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

open M46

theorem exists_seed_young_ordinary_birth_volume
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (N : RepairedNoncollapseInductionData S)
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    {A alpha B : ℝ} (hA : 1 ≤ A) (halpha : 0 < alpha) (hB : 1 ≤ B) :
    ∃ V : ℝ, 0 < V ∧ ∀ rNext : ℝ, 0 < rNext → rNext ≤ p.r (Fin.last p.i) →
      ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
        ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
          ObservedInputs p rNext cutoff F O →
        ∀ (C : GeneralizedSliceCarrier.{u}) (origin scale : ℝ) (I : Set ℝ)
          (U : TopologicalSpace.Opens C.carrier), IsCompact (U : Set C.carrier) →
        ∀ (e : SurgeryFlowCylinder F C origin scale I U) (s : ℝ) (hs : s ∈ I),
        ∀ d : ℝ, 0 < d → d ≤ rNext ^ 2 / (32 * A) →
          origin + s / scale + d ∈ Ico (surgeryEpochStart p.i) O.H →
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
  obtain ⟨k, sigma, lambda, hk, _hsigma, hlambda, _hlambdaSmall, hvolume⟩ :=
    exists_seed_observed_scaled_birth_density P S N p hp
  obtain ⟨M, hM, _hMone, _hMB, hscales⟩ :=
    exists_seed_young_birth_scale hA halpha hB hlambda
  let V := k * lambda ^ 3 / (64 * Real.sqrt M ^ 3)
  have hV : 0 < V := by dsimp only [V]; positivity
  have hApos : 0 < A := zero_lt_one.trans_le hA
  refine ⟨V, hV, ?_⟩
  intro rNext hrNext hrLast
  obtain ⟨cutoff, hcutoff, hcutoffLast, hsearch⟩ := hvolume rNext hrNext hrLast
  refine ⟨cutoff, hcutoff, hcutoffLast, ?_⟩
  intro F O inputs C origin scale I U hcompact e s hs d hd hyoung hfuture
    g D hmetric hread q hscalar hbirth
  let : CompactSpace U := isCompact_iff_compactSpace.mp hcompact
  let H := M / d
  let r := lambda / Real.sqrt H
  let R := Real.sqrt (alpha * d) / (4 * A)
  have hR : 0 < R := by dsimp only [R]; positivity
  obtain ⟨hH, hlevel, hr, hrR, hscalarScale, hrUnits⟩ := hscales d rNext hd hrNext hyoung
  obtain ⟨_hduration, _hr, _hrNext, hdNext, volume⟩ := hsearch H hH hlevel
  have hyoung32 : d ≤ rNext ^ 2 / 32 := by
    have h := (le_div_iff₀ (by positivity : 0 < 32 * A)).mp hyoung
    nlinarith only [h, hA, hd]
  have hwindow : Icc (origin + s / scale - sigma / H) (origin + s / scale) ⊆
      surgeryObservationInterval O ∩ Ici (surgeryEpochStart (p.i - 1)) := by
    simpa only [add_sub_cancel_right] using
      seed_young_birth_search_window p hrNext hrLast hfuture hd.le hyoung32 hdNext
  have hphysical := seed_ordinary_scalar_ball_bound U e s hs g D hmetric hread q hR hscalar
  have hphysicalSmall : ∀ y ∈ (F.metric (origin + s / scale)).ball (e.forward s hs q.val) r,
      (F.connection (origin + s / scale)).scalarCurvature y ≤ 2 * H := by
    intro y hy
    exact (hphysical y (hy.trans_le (ENNReal.ofReal_le_ofReal hrR))).trans hscalarScale
  have hv := volume F O inputs (origin + s / scale) hwindow (e.forward s hs q.val)
    hphysicalSmall hbirth
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
