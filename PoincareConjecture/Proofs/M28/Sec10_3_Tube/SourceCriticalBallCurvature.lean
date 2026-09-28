import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallScalar
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CriticalBallLocalShiProducer










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily




theorem exists_source_criticalBall_curvature_accuracy
    (P : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 1000 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E)
        (T : ∀ k, SourceTubeData (H.segment k)),
        epsilon ≤ epsilon₀ → ∀ {A1 : ℝ} (hA1 : 0 < A1)
          (D : ∀ k, LeviCivitaData (H.tubeCriticalMetric T A1 k)),
          (∀ r < A1, tube.eventuallyRadiusBound
            (fun k x => ((H.tubeMetric T k).edist (H.tubeBase T k) x).toReal)
            (fun k x => (H.tubeConnection T k).scalarCurvature x) r) →
          ∀ delta : ℝ, 0 < delta → ∀ l : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in atTop,
            ∀ x ∈ regularComponent (H.tubeCriticalMetric T A1 k)
              (H.tubeCriticalBase T A1 hA1 k) delta,
              (D k).curvatureDerivativeNorm l x ≤ B := by
  obtain ⟨epsilonR, hRpos, hRsmall, hregular⟩ :=
    exists_source_criticalBall_scalar_accuracy.{u}
  obtain ⟨epsilonS, hSpos, _hSsmall, hshi⟩ :=
    exists_criticalBallPointwiseShi_uniform_accuracy P
  refine ⟨min epsilonR epsilonS, lt_min hRpos hSpos,
    (min_le_left _ _).trans hRsmall, ?_⟩
  intro epsilon C A E H T hepsilon A1 hA1 D hcrit delta hdelta l
  obtain ⟨K, _hK, hscalar⟩ := hregular H T
    (hepsilon.trans (min_le_left _ _)) hcrit delta hdelta
  obtain ⟨B, hB, hbound⟩ := hshi H T
    (hepsilon.trans (min_le_right _ _)) K l
  refine ⟨B, hB, ?_⟩
  filter_upwards [hscalar] with k hk x hx
  rw [intrinsicOpenMetric_curvatureDerivativeNorm (g := H.tubeMetric T k)
    (V := H.tubeCriticalRegion T A1 k) (DU := D k)
    (D := H.tubeConnection T k) l x]
  exact hbound k x (hk x (regularComponent_subset _ _ _ hx))

end PoincareConjecture.M28.CounterexampleNeckFamily
