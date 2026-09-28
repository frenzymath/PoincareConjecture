import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Cap.Transport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.CompactCoverage












set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace

namespace M23TerminalMetricConvergence




theorem exists_cap_transport_with_strong_collar
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 400 ∧
      ∀ kappa : ℝ, 0 < kappa → ∀ C₀ : ℝ, 0 < C₀ →
        ∃ C : ℝ, 0 < C ∧
          ∀ {S : NormalizedKappaSolutionSequence kappa}
            {G : M23InteriorConvergence S}
            {e : ∀ j, NormalizedKappaSpacetimeEmbedding
              (source := S.term (G.subsequence j)) (target := G.limit)
              (Iic 0 ×ˢ G.exhaustion j)},
            M23TerminalMetricConvergence G e →
            (∀ k (t : ℝ), t ≤ 0 → ∀ x ∈ G.exhaustion k,
              ((e k).toFun (t, x)).2 = ((e k).toFun (0, x)).2) →
            ∀ A : CapCertificate (G.limit.flow.flow.metric 0),
              A.epsilon ≤ epsilon₀ → A.cap_constant ≤ C₀ →
              ∀ delta : ℝ, delta < A.epsilon →
                (∀ x ∈ closure A.carrier \ A.core,
                  ∃ N : StrongEvolvingNeck G.limit.flow 0 delta, N.center = x) →
                ∀ᶠ k in atTop,
                  ∃ B : CapCertificate ((S.term (G.subsequence k)).flow.flow.metric 0),
                    B.epsilon = A.epsilon ∧ B.cap_constant = C ∧
                    B.carrier = (fun x => ((e k).toFun (0, x)).2) '' A.carrier ∧
                    B.core = (fun x => ((e k).toFun (0, x)).2) '' A.core ∧
                    B.closed_core = (fun x => ((e k).toFun (0, x)).2) '' A.closed_core ∧
                    B.boundary_sphere = (fun x => ((e k).toFun (0, x)).2) '' A.boundary_sphere ∧
                    B.model_kind = A.model_kind ∧
                    B.connection = (S.term (G.subsequence k)).flow.flow.connection 0 ∧
                    ∀ x ∈ B.carrier \ B.core,
                      ∃ N : StrongEvolvingNeck (S.term (G.subsequence k)).flow 0 A.epsilon,
                        N.center = x := by
  obtain ⟨epsilon₀, hepsilon₀, hsmall, htransport⟩ := exists_cap_transport P
  refine ⟨epsilon₀, hepsilon₀, hsmall, ?_⟩
  intro kappa hkappa C₀ hC₀
  obtain ⟨C, hC, hcap⟩ := htransport kappa hkappa C₀ hC₀
  refine ⟨C, hC, ?_⟩
  intro S G e hconv hfixed A hepsilon hAC₀ delta hdelta hneck
  have hfull : ∀ k (s t : ℝ) (x : G.limit.carrier.carrier),
      s ≤ 0 → t ≤ 0 → x ∈ G.exhaustion k →
        ((e k).toFun (s, x)).2 = ((e k).toFun (t, x)).2 := by
    intro k s t x hs ht hx
    exact (hfixed k s hs x hx).trans (hfixed k t ht x hx).symm
  have hcompact : IsCompact (closure A.carrier \ A.core) :=
    (A.isCompact_closure_carrier (G.limit.flow.complete 0 le_rfl)).diff A.isOpen_core
  have heps : A.epsilon < 1 / 200 :=
    (hepsilon.trans hsmall).trans_lt (by norm_num)
  filter_upwards [hcap hconv hfixed A hepsilon hAC₀,
    hconv.eventually_transported_strongNecks_on_compact hfull hcompact hdelta heps hneck]
    with k hk hcoverage
  obtain ⟨B, hBε, hBC, hcarrier, hcore, hclosed, hboundary, hmodel, hconnection⟩ := hk
  refine ⟨B, hBε, hBC, hcarrier, hcore, hclosed, hboundary, hmodel, hconnection, ?_⟩
  intro y hy
  obtain ⟨x, hxA, hxy⟩ := hcarrier.subset hy.1
  have hxcore : x ∉ A.core := by
    intro hx
    exact hy.2 (hcore.symm ▸ ⟨x, hx, hxy⟩)
  obtain ⟨N, hN⟩ := hcoverage x ⟨subset_closure hxA, hxcore⟩
  exact ⟨N, hN.trans hxy⟩

end M23TerminalMetricConvergence

end PoincareConjecture
