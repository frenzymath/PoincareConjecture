import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Cap.Construction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.FullDomainStability

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace

namespace M23TerminalMetricConvergence

theorem exists_cap_transport (P : M26CanonicalNeighborhoodPredecessors.{u}) :
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
              ∀ᶠ k in atTop,
                ∃ B : CapCertificate ((S.term (G.subsequence k)).flow.flow.metric 0),
                  B.epsilon = A.epsilon ∧ B.cap_constant = C ∧
                  B.carrier = (fun x => ((e k).toFun (0, x)).2) '' A.carrier ∧
                  B.core = (fun x => ((e k).toFun (0, x)).2) '' A.core ∧
                  B.closed_core = (fun x => ((e k).toFun (0, x)).2) '' A.closed_core ∧
                  B.boundary_sphere = (fun x => ((e k).toFun (0, x)).2) '' A.boundary_sphere ∧
                  B.model_kind = A.model_kind ∧
                  B.connection = (S.term (G.subsequence k)).flow.flow.connection 0 := by
  obtain ⟨epsilon₀, hepsilon₀, _, htransport⟩ :=
    exists_cap_transport_of_terminal_neck_comparisons P
  refine ⟨min epsilon₀ (1 / 400), lt_min hepsilon₀ (by norm_num), min_le_right _ _, ?_⟩
  intro kappa hkappa C₀ hC₀
  obtain ⟨C, hC, hcap⟩ := htransport kappa hkappa C₀ hC₀
  refine ⟨C, hC, ?_⟩
  intro S G e hconv hfixed A hepsilon hAC₀
  have hfull : ∀ k (s t : ℝ) (x : G.limit.carrier.carrier),
      s ≤ 0 → t ≤ 0 → x ∈ G.exhaustion k →
        ((e k).toFun (s, x)).2 = ((e k).toFun (t, x)).2 := by
    intro k s t x hs ht hx
    exact (hfixed k s hs x hx).trans (hfixed k t ht x hx).symm
  have hsmall : A.epsilon < 1 / 200 :=
    (hepsilon.trans (min_le_right _ _)).trans_lt (by norm_num)
  have hcompact := A.isCompact_closure_carrier (G.limit.flow.complete 0 le_rfl)
  have hend : IsCompact (closure A.end_neck.carrier) :=
    hcompact.of_isClosed_subset isClosed_closure (closure_mono A.end_neck_subset)
  have hboundary : IsCompact (closure A.boundary_neck.carrier) :=
    hcompact.of_isClosed_subset isClosed_closure (closure_mono A.boundary_neck_subset)
  apply hcap hconv hfixed A (hepsilon.trans (min_le_left _ _)) hAC₀
  · simpa only [A.end_neck_epsilon] using
      hconv.eventually_terminalNeck_full_scalarClose hfull A.end_neck hend
        (by simpa only [A.end_neck_epsilon] using hsmall)
  · simpa only [A.boundary_neck_epsilon] using
      hconv.eventually_terminalNeck_full_scalarClose hfull A.boundary_neck hboundary
        (by simpa only [A.boundary_neck_epsilon] using hsmall)

end M23TerminalMetricConvergence

end PoincareConjecture
