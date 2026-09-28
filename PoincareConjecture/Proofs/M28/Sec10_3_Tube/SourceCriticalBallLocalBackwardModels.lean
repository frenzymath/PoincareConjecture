import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallPositiveBackwardProducer
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CanonicalBackwardModel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

set_option maxHeartbeats 1600000 in

theorem exists_source_criticalBall_local_backward_models_accuracy
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
          ∀ (_D₀ : LeviCivitaData G.limitMetric) (q : G.limitCarrier.carrier)
            (U : Set G.limitCarrier.carrier), IsOpen U → q ∈ U →
            Nonempty (LocalNonnegativeBackwardModel G.limitMetric U q) := by
  obtain ⟨epsilon₀, hpos, hsmall, hsource⟩ :=
    exists_source_criticalBall_positive_backward_limit_accuracy P
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro epsilon C A E H T hepsilon A1 hA1 phi hphi G
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro D₀ q U hU hq
  obtain ⟨D, L, hnonnegative⟩ := hsource H T hepsilon A1 hA1 phi hphi G D₀ q
  have hcenter : extChartAt (𝓡 3) q q ∈ D.limitDomain := mem_ball_self D.radius_pos
  have htarget : D.limitDomain ⊆ (extChartAt (𝓡 3) q).target :=
    D.limitDomain_subset_domain.trans (ball_subset_closedBall.trans D.target)
  exact exists_localNonnegativeBackwardModel_of_chart_flow G.limitMetric q
    D.limitDomain D.limitDomain_open hcenter htarget ((D₀.scalarCurvature q)⁻¹ / 8)
    (by linarith [D.scale_pos]) L.flow L.terminal_coefficients hnonnegative hU hq

end PoincareConjecture.M28.CounterexampleNeckFamily
