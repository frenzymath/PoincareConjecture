import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.LocalBounds.Limit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.ParabolicNoncollapse
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.ScalarBuffer












set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.NormalizedKappaSolutionSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

variable {kappa : ℝ} (S : NormalizedKappaSolutionSequence kappa)

local instance constructionSourceConnected (k : ℕ) : ConnectedSpace (S.term k).carrier.carrier :=
  (S.term k).connectedSpace



theorem exists_complete_noncollapsed_interior_geometric_limit
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hlocal : M23LocalCurvatureEstimate S) :
    ∃ G : AncientPointedGeometricConvergence (fun k => (S.term k).carrier)
        (fun k t => (S.term k).flow.flow.metric (t - 1)) (fun k => (S.term k).base) 1,
      (∀ t : ℝ, t < 1 → G.limitCarrier.metricComplete (G.limitFlow.metric t)) ∧
      (∀ t : ℝ, t < 1 → ∀ x : G.limitCarrier.carrier,
        (G.limitFlow.connection t).NonnegativeCurvatureOperator x) ∧
      (∃ s ∈ Ioo (0 : ℝ) 1, 0 < (G.limitFlow.connection s).curvatureTensorNorm G.base) ∧
      ∀ t : ℝ, t < 1 → ∀ p : G.limitCarrier.carrier, ∀ r : ℝ, 0 < r →
        (∀ u ∈ Ioc (t - r ^ 2) t, ∀ x ∈ (G.limitFlow.metric t).ball p r,
          |(G.limitFlow.connection u).curvatureTensorNorm x| ≤ r⁻¹ ^ 2) →
        ENNReal.ofReal (kappa * r ^ 3) ≤ calibratedMetricVolume (G.limitFlow.metric t)
          ((G.limitFlow.metric t).ball p r) := by
  have hcontrol := m23AllTimeCurvatureControl_of_local S P hlocal
  obtain ⟨G, hreference⟩ := S.exists_complete_interior_geometric_limit P hcontrol
  have hcomplete := S.interiorLimit_complete G P hcontrol hreference
  refine ⟨G, hcomplete, S.interiorLimit_nonnegativeCurvatureOperator G, ?_, ?_⟩
  · obtain ⟨δ, hδ, hδone, hbuffer⟩ := S.exists_base_scalar_positive_time_buffer P hcontrol
    refine ⟨1 - δ, ⟨by linarith, by linarith⟩, ?_⟩
    apply S.interiorLimit_base_curvatureTensorNorm_pos_of_scalar_buffer G
      (by linarith : 1 - δ < 1) (by norm_num : (0 : ℝ) < 1 / 2)
    exact Eventually.of_forall fun k => hbuffer k (1 - δ - 1) ⟨by linarith, by linarith⟩
  · intro t ht p r hr hcurv
    exact S.interiorLimit_noncollapsed_ball G hcomplete ht p hr hcurv

end PoincareConjecture.NormalizedKappaSolutionSequence
