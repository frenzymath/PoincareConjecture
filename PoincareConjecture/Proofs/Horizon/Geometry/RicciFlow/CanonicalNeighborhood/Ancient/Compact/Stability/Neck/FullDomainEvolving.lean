import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.FullDomainFamilyComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.FullDomainSmoothness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.Jets.CenteredError
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.Jets.FullDomainEvolving

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

theorem eventually_terminalNeck_full_evolving_centeredErrorJets
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ k (s t : ℝ) (x : G.limit.carrier.carrier),
      s ≤ 0 → t ≤ 0 → x ∈ G.exhaustion k →
        ((e k).toFun (s, x)).2 = ((e k).toFun (t, x)).2)
    (N : EpsilonNeck (G.limit.flow.flow.metric 0))
    (hcompact : IsCompact (closure N.carrier)) (hsmall : N.epsilon < 1 / 200)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k in atTop, ∀ u ∈ Ioc (-1 : ℝ) 0, ∀ z : RoundCylinderSpace,
      z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ∀ j : ℕ, j ≤ ⌊N.epsilon⁻¹⌋₊ →
        ‖iteratedFDeriv ℝ j (fun p =>
          centeredCylinderError
            (roundCylinderPullback ((S.term (G.subsequence k)).flow.flow.metric u)
              (G.terminalNeckEmbedding e N N.epsilon k)) z.1 z.2 p -
          centeredCylinderError
            (roundCylinderPullback (G.limit.flow.flow.metric u)
              N.coordinate_map) z.1 z.2 p) 0‖ ≤ η := by
  filter_upwards [hconv.eventually_centeredNeck_jets_full_domain_uniform_time
      hfixed N hcompact hsmall hη,
    G.eventually_terminalNeckEmbedding_full e N hcompact] with k hjet hcoords u hu z hz j hj
  have heq := centeredCylinderError_difference_jet_eq
    ((S.term (G.subsequence k)).flow.flow.metric u) (G.limit.flow.flow.metric u)
    (G.terminalNeckEmbedding e N N.epsilon k) N.coordinate_map
    1 1 z.1 z.2 (isOpen_univ.prod isOpen_Ioo) ⟨mem_univ _, hz⟩
    hcoords.2.2.1 N.coordinate_map_smooth j
  simp only [one_mul, one_smul] at heq
  rw [heq]
  exact hjet u hu z hz j hj

theorem eventually_terminalNeck_full_familyClose
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ k (s t : ℝ) (x : G.limit.carrier.carrier),
      s ≤ 0 → t ≤ 0 → x ∈ G.exhaustion k →
        ((e k).toFun (s, x)).2 = ((e k).toFun (t, x)).2)
    (N : EpsilonNeck (G.limit.flow.flow.metric 0))
    (hcompact : IsCompact (closure N.carrier)) (hsmall : N.epsilon < 1 / 200)
    (hclose : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (fun u => roundCylinderPullback (G.limit.flow.flow.metric u) N.coordinate_map)) :
    ∀ᶠ k in atTop, RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (fun u => roundCylinderPullback ((S.term (G.subsequence k)).flow.flow.metric u)
        (G.terminalNeckEmbedding e N N.epsilon k)) := by
  apply TerminalNeck.eventually_roundCylinderFamilyClose_of_centeredDifferenceJets_fullDomain
    N.epsilon_pos hclose
  · filter_upwards [G.eventually_terminalNeck_full_tensorSmoothOn e N hcompact] with k hk u hu
    simpa only [one_mul] using hk u 1
  · exact fun _ hη => hconv.eventually_terminalNeck_full_evolving_centeredErrorJets
      hfixed N hcompact hsmall hη

end M23TerminalMetricConvergence
end PoincareConjecture
