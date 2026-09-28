import PoincareConjecture.Proofs.Ch01.CurvatureConnection
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Scalar.Terminal
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.CylinderCoefficients










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace

namespace M23InteriorConvergence

variable {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
  (G : M23InteriorConvergence S)
  (e : ∀ j, NormalizedKappaSpacetimeEmbedding
    (source := S.term (G.subsequence j)) (target := G.limit) (Iic 0 ×ˢ G.exhaustion j))



theorem eventually_terminalNeck_full_tensorSmoothOn
    (N : EpsilonNeck (G.limit.flow.flow.metric 0)) (hN : IsCompact (closure N.carrier)) :
    ∀ᶠ k in atTop, ∀ t s : ℝ, RoundCylinderTensorSmoothOn N.epsilon (fun z v w =>
      s * roundCylinderPullback ((S.term (G.subsequence k)).flow.flow.metric t)
        (G.terminalNeckEmbedding e N N.epsilon k) z v w) := by
  filter_upwards [G.eventually_terminalNeckEmbedding_full e N hN] with k hk t s
  exact roundCylinderTensorSmoothOn_smul_pullback
    ((S.term (G.subsequence k)).flow.flow.metric t) hk.2.2.1 s



theorem eventually_terminalNeck_full_scalar_tensorSmoothOn
    (N : EpsilonNeck (G.limit.flow.flow.metric 0)) (hN : IsCompact (closure N.carrier)) :
    ∀ᶠ k in atTop, RoundCylinderTensorSmoothOn N.epsilon (fun z v w =>
      ((S.term (G.subsequence k)).flow.flow.connection 0).scalarCurvature
          ((e k).toFun (0, N.center)).2 *
        roundCylinderPullback ((S.term (G.subsequence k)).flow.flow.metric 0)
          (G.terminalNeckEmbedding e N N.epsilon k) z v w) := by
  filter_upwards [G.eventually_terminalNeck_full_tensorSmoothOn e N hN] with k hk
  exact hk 0 _

end M23InteriorConvergence

namespace M23TerminalMetricConvergence

variable {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
  {G : M23InteriorConvergence S}
  {e : ∀ j, NormalizedKappaSpacetimeEmbedding
    (source := S.term (G.subsequence j)) (target := G.limit) (Iic 0 ×ˢ G.exhaustion j)}



theorem eventually_terminalNeck_full_source_scalar_positive
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ k (s t : ℝ) (x : G.limit.carrier.carrier),
      s ≤ 0 → t ≤ 0 → x ∈ G.exhaustion k →
        ((e k).toFun (s, x)).2 = ((e k).toFun (t, x)).2)
    (N : EpsilonNeck (G.limit.flow.flow.metric 0)) (hN : IsCompact (closure N.carrier)) :
    ∀ᶠ k in atTop,
      (G.terminalNeckEmbedding e N N.epsilon k).source = N.cylinderDomain ∧
      0 < ((S.term (G.subsequence k)).flow.flow.connection 0).scalarCurvature
        ((e k).toFun (0, N.center)).2 := by
  have hR : 0 < (G.limit.flow.flow.connection 0).scalarCurvature N.center := by
    rw [← N.connection.scalarCurvature_eq (G.limit.flow.flow.connection 0)]
    exact N.scalar_center_pos
  have hprod := hconv.tendsto_terminal_scalarCurvature_prod
    (fun k t ht x hx => hfixed k t 0 x ht le_rfl hx) N.center
  have hp := hprod.comp (tendsto_id.prodMk tendsto_const_nhds)
  filter_upwards [G.eventually_terminalNeckEmbedding_full e N hN,
    hp.eventually (lt_mem_nhds hR)] with k hk hpos
  exact ⟨hk.1, hpos⟩

end M23TerminalMetricConvergence

end PoincareConjecture
