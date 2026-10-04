import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.CriticalBall.SourceCriticalBallBackwardPositivity

/-!
# Actual nonnegative local backward models from the source family

The source-family producer supplies the curvature bound before extraction.
Original pinching then proves nonnegative curvature of the same genuine
backward limit, whose terminal metric remains the retained spatial metric.
Morgan--Tian Proposition 5.14 and Claim 10.11, pp. 90-91 and 255;
M28 derivation 78.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M28.CounterexampleNeckFamily

set_option maxHeartbeats 1400000 in
-- Retain the same dependent source data, extracted flow and curvature bound.
/-- A universal source accuracy constructs an actual nonnegative backward
chart limit with exact terminal spatial metric. The curvature bound is
produced from the source, not supplied as an extra assumption (derivation 78). -/
theorem exists_source_criticalBall_positive_backward_limit_accuracy
    (P : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 1000 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E) (T : ∀ k, SourceTubeData (H.segment k)),
        epsilon ≤ epsilon₀ → ∀ (A1 : ℝ) (hA1 : 0 < A1) (phi : ℕ → ℕ),
          StrictMono phi → ∀ (G : RegularPointedMetricConvergence
            (fun k => H.tubeCriticalMetric T A1 (phi k))
            (fun k => H.tubeCriticalBase T A1 hA1 (phi k))),
          letI := G.limitCarrier.topologicalSpace
          letI := G.limitCarrier.chartedSpace
          letI := G.limitCarrier.isManifold
          ∀ (D₀ : LeviCivitaData G.limitMetric) (q : G.limitCarrier.carrier),
            ∃ D : CriticalBallBackwardChartData H T A1 hA1 phi G q
              (D₀.scalarCurvature q)⁻¹,
            ∃ L : CriticalBallBackwardChartData.BackwardChartLimit D,
              letI := D.limitDomain_open.isOpenEmbedding_subtypeVal.singletonChartedSpace
              letI := D.limitDomain_open.isOpenEmbedding_subtypeVal.isManifold_singleton
                (I := 𝓡 3) (n := ∞)
              ∀ t ∈ Icc (-((D₀.scalarCurvature q)⁻¹ / 8)) 0,
                ∀ x : D.limitDomain, (L.flow.connection t).NonnegativeCurvatureOperator x := by
  obtain ⟨epsilon₀, hpos, hsmall, hsource⟩ :=
    exists_source_criticalBall_backward_family_accuracy P
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro epsilon C A E H T hepsilon A1 hA1 phi hphi G
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro D₀ q
  obtain ⟨D, ⟨K, hK, hcurv⟩, hderiv⟩ := hsource H T hepsilon A1 hA1 phi G D₀ q
  obtain ⟨L⟩ := D.exists_backward_limit hK.le hcurv hderiv
  exact ⟨D, L, L.nonnegativeCurvatureOperator P hphi hK.le hcurv⟩

end PoincareMT.M28.CounterexampleNeckFamily
