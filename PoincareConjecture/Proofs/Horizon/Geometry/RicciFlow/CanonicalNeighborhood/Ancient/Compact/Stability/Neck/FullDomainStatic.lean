import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.FullDomainStability

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace

namespace M23TerminalMetricConvergence

variable {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
  {G : M23InteriorConvergence S}
  {e : ∀ j, NormalizedKappaSpacetimeEmbedding
    (source := S.term (G.subsequence j)) (target := G.limit) (Iic 0 ×ˢ G.exhaustion j)}

theorem eventually_terminalStaticNeck_full_domain
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ k (s t : ℝ) (x : G.limit.carrier.carrier),
      s ≤ 0 → t ≤ 0 → x ∈ G.exhaustion k →
        ((e k).toFun (s, x)).2 = ((e k).toFun (t, x)).2)
    (N : EpsilonNeck (G.limit.flow.flow.metric 0))
    (hN : IsCompact (closure N.carrier)) (hsmall : N.epsilon < 1 / 200) :
    ∀ᶠ k in atTop,
      ∃ B : EpsilonNeck ((S.term (G.subsequence k)).flow.flow.metric 0),
        B.epsilon = N.epsilon ∧
        B.center = ((e k).toFun (0, N.center)).2 ∧
        B.connection = (S.term (G.subsequence k)).flow.flow.connection 0 ∧
        B.scale = (((S.term (G.subsequence k)).flow.flow.connection 0).scalarCurvature
          ((e k).toFun (0, N.center)).2) ^ (-1 / 2 : ℝ) ∧
        B.coordinate_map = G.terminalNeckEmbedding e N N.epsilon k ∧
        B.coordinate_inverse = (G.terminalNeckEmbedding e N N.epsilon k).symm ∧
        B.central_sphere = (fun x => ((e k).toFun (0, x)).2) '' N.central_sphere ∧
        B.carrier = (fun x => ((e k).toFun (0, x)).2) '' N.carrier ∧
        ∀ a b : ℝ, B.region a b = (fun x => ((e k).toFun (0, x)).2) '' N.region a b := by
  obtain ⟨k₀, hk₀⟩ := G.exists_exhaustion_superset hN
  filter_upwards [hconv.eventually_terminalNeck_full_scalarClose hfixed N hN hsmall,
    hconv.eventually_terminalNeck_full_source_scalar_positive hfixed N hN,
    eventually_ge_atTop k₀] with k hclose hcoords hk
  have hsource := hcoords.1
  have hR := hcoords.2
  have hstage : N.carrier ⊆ G.exhaustion k :=
    subset_closure.trans (hk₀.trans (G.exhaustion_monotone hk))
  let B := G.terminalStaticNeck e N N.epsilon_pos N.epsilon_lt_half k hsource hR hclose
  refine ⟨B, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · exact G.terminalStaticNeck_central_sphere e N N.epsilon_pos N.epsilon_lt_half k
      hsource hR hclose
  · exact G.terminalStaticNeck_carrier_of_epsilon_eq e N N.epsilon_pos N.epsilon_lt_half k
      hsource hR hclose rfl hstage
  · intro a b
    exact G.terminalStaticNeck_region_of_epsilon_eq e N N.epsilon_pos N.epsilon_lt_half k
      hsource hR hclose rfl hstage a b

end M23TerminalMetricConvergence
end PoincareConjecture
