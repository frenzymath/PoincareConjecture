import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallBackwardLimit











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily




theorem exists_source_criticalBall_backward_limit_accuracy
    (P : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 1000 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E) (T : ∀ k, SourceTubeData (H.segment k)),
        epsilon ≤ epsilon₀ → ∀ (A1 : ℝ) (hA1 : 0 < A1) (phi : ℕ → ℕ)
          (G : RegularPointedMetricConvergence
            (fun k => H.tubeCriticalMetric T A1 (phi k))
            (fun k => H.tubeCriticalBase T A1 hA1 (phi k))),
          letI := G.limitCarrier.topologicalSpace
          letI := G.limitCarrier.chartedSpace
          letI := G.limitCarrier.isManifold
          ∀ (D₀ : LeviCivitaData G.limitMetric) (q : G.limitCarrier.carrier),
            ∃ D : CriticalBallBackwardChartData H T A1 hA1 phi G q
              (D₀.scalarCurvature q)⁻¹,
              Nonempty (CriticalBallBackwardChartData.BackwardChartLimit D) := by
  obtain ⟨epsilon₀, hpos, hsmall, hsource⟩ :=
    exists_source_criticalBall_backward_family_accuracy P
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro epsilon C A E H T hepsilon A1 hA1 phi G
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro D₀ q
  obtain ⟨D, ⟨K, hK, hcurv⟩, hderiv⟩ := hsource H T hepsilon A1 hA1 phi G D₀ q
  exact ⟨D, D.exists_backward_limit hK.le hcurv hderiv⟩

end PoincareConjecture.M28.CounterexampleNeckFamily
