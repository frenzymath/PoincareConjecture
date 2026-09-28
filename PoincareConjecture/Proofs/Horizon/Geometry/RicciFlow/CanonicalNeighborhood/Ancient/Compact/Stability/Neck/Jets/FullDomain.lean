import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.Jets.Terminal
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.Jets.Parametrization

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace

local notation "E" => EuclideanSpace ℝ (Fin 3)

namespace M23TerminalMetricConvergence

open MetricSurgery

variable {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
  {G : M23InteriorConvergence S}
  {e : ∀ j, NormalizedKappaSpacetimeEmbedding
    (source := S.term (G.subsequence j)) (target := G.limit) (Iic 0 ×ˢ G.exhaustion j)}

theorem eventually_normalized_centeredNeck_jets_full_domain
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ k (s t : ℝ) (x : G.limit.carrier.carrier),
      s ≤ 0 → t ≤ 0 → x ∈ G.exhaustion k →
        ((e k).toFun (s, x)).2 = ((e k).toFun (t, x)).2)
    (N : EpsilonNeck (G.limit.flow.flow.metric 0))
    (hcompact : IsCompact (closure N.carrier)) (hsmall : N.epsilon < 1 / 200)
    {s : ℕ → ℝ} {s₀ : ℝ} (hs : Tendsto s atTop (𝓝 s₀))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k in atTop, ∀ z : RoundCylinderSpace,
      z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ∀ j : ℕ, j ≤ ⌊N.epsilon⁻¹⌋₊ →
        ‖iteratedFDeriv ℝ j (fun y => s k •
          ((S.term (G.subsequence k)).flow.flow.metric 0).parametrizedCoefficients
            (fun x => ((e k).toFun (0, centeredNeckLift N z.1 z.2 x)).2) y -
          s₀ • (G.limit.flow.flow.metric 0).parametrizedCoefficients
            (centeredNeckLift N z.1 z.2) y) 0‖ ≤ η := by
  classical
  let : LocallyCompactSpace G.limit.carrier.carrier :=
    ChartedSpace.locallyCompactSpace E _
  let m := ⌊N.epsilon⁻¹⌋₊
  have hm : 1 ≤ m := by
    have htwo := N.two_le_floor_inv_epsilon
    omega
  have hlocal (q : G.limit.carrier.carrier) :
      ∃ U ∈ 𝓝 q, ∀ᶠ k in atTop, ∀ z : RoundCylinderSpace,
        z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ → N.coordinate_map z ∈ U →
        ∀ j : ℕ, j ≤ m →
          ‖iteratedFDeriv ℝ j (fun y => s k •
            ((S.term (G.subsequence k)).flow.flow.metric 0).parametrizedCoefficients
              (fun x => ((e k).toFun (0, centeredNeckLift N z.1 z.2 x)).2) y -
            s₀ • (G.limit.flow.flow.metric 0).parametrizedCoefficients
              (centeredNeckLift N z.1 z.2) y) 0‖ ≤ η := by
    obtain ⟨K, hKnhds, hKchart, hK⟩ := local_compact_nhds
      ((isOpen_extChartAt_source (I := 𝓡 3) q).mem_nhds (mem_extChartAt_source q))
    obtain ⟨C, hC, hCj⟩ := exists_centeredNeckAmbientCoordinates_jet_bound
      N hsmall q hK hKchart m hm le_rfl
    let Z := {z : RoundCylinderSpace //
      z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ ∧ N.coordinate_map z ∈ K}
    let f := fun z : Z => centeredNeckLift N z.1.1 z.1.2
    have hf (z : Z) : ∃ U, IsOpen U ∧ (0 : E) ∈ U ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f z) U := by
      refine ⟨centeredNeckDomain N z.1.2, centeredNeckDomain_isOpen N z.1.2,
        zero_mem_centeredNeckDomain N z.2.1, ?_⟩
      intro y hy
      exact (centeredNeckLift_contMDiffAt N z.1.1 z.1.2 hy).contMDiffWithinAt
    have hmap (z : Z) : f z 0 ∈ K := by
      simpa only [f, centeredNeckLift_zero] using z.2.2
    have hj (z : Z) (j : ℕ) (_hj₀ : 1 ≤ j) (hj : j ≤ m + 1) :
        ‖iteratedFDeriv ℝ j ((extChartAt (𝓡 3) q) ∘ f z) 0‖ ≤ C :=
      hCj z z.2.1 z.2.2 j hj
    refine ⟨K, hKnhds, ?_⟩
    filter_upwards [hconv.eventually_normalized_parametrized_jets_at_of_chart_bound
      hfixed q hK hKchart f hf hmap m hC hj hs hη] with k hk z hz hKz j hj
    exact hk ⟨z, hz, hKz⟩ j hj
  choose U hU hbound using hlocal
  obtain ⟨t, _, ht⟩ := hcompact.elim_nhds_subcover U (fun q _ => hU q)
  filter_upwards [t.eventually_all.mpr (fun q _ => hbound q)] with k hk z hz j hj
  have hzcarrier : N.coordinate_map z ∈ closure N.carrier :=
    subset_closure (neck_coordinate_mem N z ⟨mem_univ _, hz⟩)
  obtain ⟨q, hqt, hzq⟩ := mem_iUnion₂.mp (ht hzcarrier)
  exact hk q hqt z hz hzq j hj

end M23TerminalMetricConvergence
end PoincareConjecture
