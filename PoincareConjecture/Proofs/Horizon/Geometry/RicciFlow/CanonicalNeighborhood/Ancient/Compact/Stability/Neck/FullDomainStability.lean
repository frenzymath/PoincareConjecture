import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.FullDomainComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.FullDomainSmoothness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.Jets.CenteredError
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.Jets.FullDomain
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.Static













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace

namespace M23TerminalMetricConvergence

open MetricSurgery

variable {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
  {G : M23InteriorConvergence S}
  {e : ∀ j, NormalizedKappaSpacetimeEmbedding
    (source := S.term (G.subsequence j)) (target := G.limit) (Iic 0 ×ˢ G.exhaustion j)}



theorem eventually_terminalNeck_full_centeredErrorJets
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ k (s t : ℝ) (x : G.limit.carrier.carrier),
      s ≤ 0 → t ≤ 0 → x ∈ G.exhaustion k →
        ((e k).toFun (s, x)).2 = ((e k).toFun (t, x)).2)
    (N : EpsilonNeck (G.limit.flow.flow.metric 0))
    (hcompact : IsCompact (closure N.carrier)) (hsmall : N.epsilon < 1 / 200)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k in atTop, ∀ z : RoundCylinderSpace,
      z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ∀ j : ℕ, j ≤ ⌊N.epsilon⁻¹⌋₊ →
        ‖iteratedFDeriv ℝ j (fun p =>
          centeredCylinderError (fun z v w =>
            ((S.term (G.subsequence k)).flow.flow.connection 0).scalarCurvature
                ((e k).toFun (0, N.center)).2 *
              roundCylinderPullback ((S.term (G.subsequence k)).flow.flow.metric 0)
                (G.terminalNeckEmbedding e N N.epsilon k) z v w) z.1 z.2 p -
          centeredCylinderError (fun z v w =>
            (G.limit.flow.flow.connection 0).scalarCurvature N.center *
              roundCylinderPullback (G.limit.flow.flow.metric 0)
                N.coordinate_map z v w) z.1 z.2 p) 0‖ ≤ η := by
  have hprod := hconv.tendsto_terminal_scalarCurvature_prod
    (fun k t ht x hx => hfixed k t 0 x ht le_rfl hx) N.center
  have hp : Tendsto (fun k : ℕ => (k, N.center)) atTop (atTop ×ˢ 𝓝 N.center) :=
    tendsto_id.prodMk tendsto_const_nhds
  have hscalar := hprod.comp hp
  filter_upwards [hconv.eventually_normalized_centeredNeck_jets_full_domain
      hfixed N hcompact hsmall hscalar hη,
    G.eventually_terminalNeckEmbedding_full e N hcompact] with k hjet hcoords z hz j hj
  rw [centeredCylinderError_difference_jet_eq
    ((S.term (G.subsequence k)).flow.flow.metric 0) (G.limit.flow.flow.metric 0)
    (G.terminalNeckEmbedding e N N.epsilon k) N.coordinate_map
    _ _ z.1 z.2 (isOpen_univ.prod isOpen_Ioo) ⟨mem_univ _, hz⟩
    hcoords.2.2.1 N.coordinate_map_smooth j]
  exact hjet z hz j hj




theorem eventually_terminalNeck_full_scalarClose
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ k (s t : ℝ) (x : G.limit.carrier.carrier),
      s ≤ 0 → t ≤ 0 → x ∈ G.exhaustion k →
        ((e k).toFun (s, x)).2 = ((e k).toFun (t, x)).2)
    (N : EpsilonNeck (G.limit.flow.flow.metric 0))
    (hcompact : IsCompact (closure N.carrier)) (hsmall : N.epsilon < 1 / 200) :
    ∀ᶠ k in atTop, RoundCylinderClose N.epsilon 0 (fun z v w =>
      ((S.term (G.subsequence k)).flow.flow.connection 0).scalarCurvature
          ((e k).toFun (0, N.center)).2 *
        roundCylinderPullback ((S.term (G.subsequence k)).flow.flow.metric 0)
          (G.terminalNeckEmbedding e N N.epsilon k) z v w) := by
  exact TerminalNeck.eventually_roundCylinderClose_of_centeredDifferenceJets N.epsilon_pos
    (G.terminalNeck_scalar_comparison N)
    (G.eventually_terminalNeck_full_scalar_tensorSmoothOn e N hcompact)
    (fun _ hη => hconv.eventually_terminalNeck_full_centeredErrorJets hfixed N hcompact hsmall hη)

end M23TerminalMetricConvergence
end PoincareConjecture
