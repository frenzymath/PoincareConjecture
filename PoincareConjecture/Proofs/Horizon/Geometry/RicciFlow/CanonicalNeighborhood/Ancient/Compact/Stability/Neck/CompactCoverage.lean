import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.TransportedCenters











set_option autoImplicit false

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



theorem eventually_transported_strongNecks_on_compact
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ k (s t : ℝ) (x : G.limit.carrier.carrier),
      s ≤ 0 → t ≤ 0 → x ∈ G.exhaustion k →
        ((e k).toFun (s, x)).2 = ((e k).toFun (t, x)).2)
    {Q : Set G.limit.carrier.carrier} (hQ : IsCompact Q)
    {δ ε : ℝ} (hδε : δ < ε) (hεsmall : ε < 1 / 200)
    (hneck : ∀ x ∈ Q, ∃ N : StrongEvolvingNeck G.limit.flow 0 δ, N.center = x) :
    ∀ᶠ k in atTop, ∀ x ∈ Q,
      ∃ N : StrongEvolvingNeck (S.term (G.subsequence k)).flow 0 ε,
        N.center = ((e k).toFun (0, x)).2 := by
  classical
  have hlocal (x : Q) : ∃ U : Set G.limit.carrier.carrier,
      IsOpen U ∧ (x : G.limit.carrier.carrier) ∈ U ∧
        ∀ᶠ k in atTop, ∀ y ∈ U,
          ∃ N : StrongEvolvingNeck (S.term (G.subsequence k)).flow 0 ε,
            N.center = ((e k).toFun (0, y)).2 := by
    obtain ⟨N, hN⟩ := hneck x x.property
    obtain ⟨U, hU, hcenter, hsource⟩ :=
      hconv.exists_open_eventually_transported_strongNeck_centers hfixed N hδε hεsmall
    exact ⟨U, hU, hN ▸ hcenter, hsource⟩
  choose U hU hcenter hsource using hlocal
  obtain ⟨t, ht⟩ := hQ.elim_finite_subcover U hU
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hcenter ⟨x, hx⟩⟩)
  filter_upwards [t.eventually_all.mpr (fun x _ => hsource x)] with k hk x hx
  obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.mp (ht hx)
  exact hk y hyt x hxy

end M23TerminalMetricConvergence

end PoincareConjecture
