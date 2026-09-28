import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.Jets.Evolving
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



theorem eventually_movingTime_centeredNeck_jets_full_domain_on_compact
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ k (s t : ℝ) (x : G.limit.carrier.carrier),
      s ≤ 0 → t ≤ 0 → x ∈ G.exhaustion k →
        ((e k).toFun (s, x)).2 = ((e k).toFun (t, x)).2)
    (N : EpsilonNeck (G.limit.flow.flow.metric 0))
    (hcompact : IsCompact (closure N.carrier)) (hsmall : N.epsilon < 1 / 200)
    {J : Set ℝ} (hJ : IsCompact J) (hJtime : J ⊆ Iic 0)
    (tau : ℕ → ℝ) (htau : ∀ k, tau k ∈ J)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k in atTop, ∀ z : RoundCylinderSpace,
      z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ∀ j : ℕ, j ≤ ⌊N.epsilon⁻¹⌋₊ →
        ‖iteratedFDeriv ℝ j (fun y =>
          ((S.term (G.subsequence k)).flow.flow.metric (tau k)).parametrizedCoefficients
            (fun x => ((e k).toFun (0, centeredNeckLift N z.1 z.2 x)).2) y -
          (G.limit.flow.flow.metric (tau k)).parametrizedCoefficients
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
          ‖iteratedFDeriv ℝ j (fun y =>
            ((S.term (G.subsequence k)).flow.flow.metric (tau k)).parametrizedCoefficients
              (fun x => ((e k).toFun (0, centeredNeckLift N z.1 z.2 x)).2) y -
            (G.limit.flow.flow.metric (tau k)).parametrizedCoefficients
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
    filter_upwards [hconv.eventually_movingTime_parametrized_jets_at_of_chart_bound_on_compact
      hfixed q hK hKchart f hf hmap m hC hj hJ hJtime tau htau hη] with k hk z hz hKz j hj
    exact hk ⟨z, hz, hKz⟩ j hj
  choose U hU hbound using hlocal
  obtain ⟨t, _, ht⟩ := hcompact.elim_nhds_subcover U (fun q _ => hU q)
  filter_upwards [t.eventually_all.mpr (fun q _ => hbound q)] with k hk z hz j hj
  have hzcarrier : N.coordinate_map z ∈ closure N.carrier :=
    subset_closure (neck_coordinate_mem N z ⟨mem_univ _, hz⟩)
  obtain ⟨q, hqt, hzq⟩ := mem_iUnion₂.mp (ht hzcarrier)
  exact hk q hqt z hz hzq j hj


theorem eventually_movingTime_centeredNeck_jets_full_domain
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ k (s t : ℝ) (x : G.limit.carrier.carrier),
      s ≤ 0 → t ≤ 0 → x ∈ G.exhaustion k →
        ((e k).toFun (s, x)).2 = ((e k).toFun (t, x)).2)
    (N : EpsilonNeck (G.limit.flow.flow.metric 0))
    (hcompact : IsCompact (closure N.carrier)) (hsmall : N.epsilon < 1 / 200)
    (tau : ℕ → ℝ) (htau : ∀ k, tau k ∈ Icc (-1 : ℝ) 0)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k in atTop, ∀ z : RoundCylinderSpace,
      z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ∀ j : ℕ, j ≤ ⌊N.epsilon⁻¹⌋₊ →
        ‖iteratedFDeriv ℝ j (fun y =>
          ((S.term (G.subsequence k)).flow.flow.metric (tau k)).parametrizedCoefficients
            (fun x => ((e k).toFun (0, centeredNeckLift N z.1 z.2 x)).2) y -
          (G.limit.flow.flow.metric (tau k)).parametrizedCoefficients
            (centeredNeckLift N z.1 z.2) y) 0‖ ≤ η := by
  exact hconv.eventually_movingTime_centeredNeck_jets_full_domain_on_compact
    hfixed N hcompact hsmall isCompact_Icc (fun _ ht => ht.2) tau htau hη


theorem eventually_centeredNeck_jets_full_domain_uniform_time_on_compact
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ k (s t : ℝ) (x : G.limit.carrier.carrier),
      s ≤ 0 → t ≤ 0 → x ∈ G.exhaustion k →
        ((e k).toFun (s, x)).2 = ((e k).toFun (t, x)).2)
    (N : EpsilonNeck (G.limit.flow.flow.metric 0))
    (hcompact : IsCompact (closure N.carrier)) (hsmall : N.epsilon < 1 / 200)
    {J : Set ℝ} (hJ : IsCompact J) (hJtime : J ⊆ Iic 0)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k in atTop, ∀ t ∈ J, ∀ z : RoundCylinderSpace,
      z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ∀ j : ℕ, j ≤ ⌊N.epsilon⁻¹⌋₊ →
        ‖iteratedFDeriv ℝ j (fun y =>
          ((S.term (G.subsequence k)).flow.flow.metric t).parametrizedCoefficients
            (fun x => ((e k).toFun (0, centeredNeckLift N z.1 z.2 x)).2) y -
          (G.limit.flow.flow.metric t).parametrizedCoefficients
            (centeredNeckLift N z.1 z.2) y) 0‖ ≤ η := by
  classical
  by_cases hne : J.Nonempty
  · obtain ⟨t₀, ht₀⟩ := hne
    let Q (k : ℕ) (t : ℝ) : Prop := ∀ z : RoundCylinderSpace,
      z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ∀ j : ℕ, j ≤ ⌊N.epsilon⁻¹⌋₊ →
        ‖iteratedFDeriv ℝ j (fun y =>
          ((S.term (G.subsequence k)).flow.flow.metric t).parametrizedCoefficients
            (fun x => ((e k).toFun (0, centeredNeckLift N z.1 z.2 x)).2) y -
          (G.limit.flow.flow.metric t).parametrizedCoefficients
            (centeredNeckLift N z.1 z.2) y) 0‖ ≤ η
    let tau (k : ℕ) : ℝ :=
      if h : ∃ t ∈ J, ¬ Q k t then Classical.choose h else t₀
    have htau (k : ℕ) : tau k ∈ J := by
      dsimp only [tau]
      split_ifs with h
      · exact (Classical.choose_spec h).1
      · exact ht₀
    have hgood : ∀ᶠ k in atTop, Q k (tau k) :=
      hconv.eventually_movingTime_centeredNeck_jets_full_domain_on_compact
        hfixed N hcompact hsmall hJ hJtime tau htau hη
    change ∀ᶠ k in atTop, ∀ t ∈ J, Q k t
    filter_upwards [hgood] with k hk t ht
    by_contra hQt
    have hbad : ∃ t ∈ J, ¬ Q k t := ⟨t, ht, hQt⟩
    have hchosen : ¬ Q k (tau k) := by
      simpa only [tau, dif_pos hbad] using (Classical.choose_spec hbad).2
    exact hchosen hk
  · filter_upwards [] with k t ht
    exact (hne ⟨t, ht⟩).elim



theorem eventually_centeredNeck_jets_full_domain_uniform_time
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ k (s t : ℝ) (x : G.limit.carrier.carrier),
      s ≤ 0 → t ≤ 0 → x ∈ G.exhaustion k →
        ((e k).toFun (s, x)).2 = ((e k).toFun (t, x)).2)
    (N : EpsilonNeck (G.limit.flow.flow.metric 0))
    (hcompact : IsCompact (closure N.carrier)) (hsmall : N.epsilon < 1 / 200)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k in atTop, ∀ t ∈ Ioc (-1 : ℝ) 0, ∀ z : RoundCylinderSpace,
      z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ∀ j : ℕ, j ≤ ⌊N.epsilon⁻¹⌋₊ →
        ‖iteratedFDeriv ℝ j (fun y =>
          ((S.term (G.subsequence k)).flow.flow.metric t).parametrizedCoefficients
            (fun x => ((e k).toFun (0, centeredNeckLift N z.1 z.2 x)).2) y -
          (G.limit.flow.flow.metric t).parametrizedCoefficients
            (centeredNeckLift N z.1 z.2) y) 0‖ ≤ η := by
  classical
  let Q (k : ℕ) (t : ℝ) : Prop := ∀ z : RoundCylinderSpace,
    z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
    ∀ j : ℕ, j ≤ ⌊N.epsilon⁻¹⌋₊ →
      ‖iteratedFDeriv ℝ j (fun y =>
        ((S.term (G.subsequence k)).flow.flow.metric t).parametrizedCoefficients
          (fun x => ((e k).toFun (0, centeredNeckLift N z.1 z.2 x)).2) y -
        (G.limit.flow.flow.metric t).parametrizedCoefficients
          (centeredNeckLift N z.1 z.2) y) 0‖ ≤ η
  let tau (k : ℕ) : ℝ :=
    if h : ∃ t ∈ Ioc (-1 : ℝ) 0, ¬ Q k t then Classical.choose h else 0
  have htau (k : ℕ) : tau k ∈ Icc (-1 : ℝ) 0 := by
    dsimp only [tau]
    split_ifs with h
    · exact ⟨(Classical.choose_spec h).1.1.le, (Classical.choose_spec h).1.2⟩
    · constructor <;> norm_num
  have hgood : ∀ᶠ k in atTop, Q k (tau k) :=
    hconv.eventually_movingTime_centeredNeck_jets_full_domain hfixed N hcompact hsmall
      tau htau hη
  change ∀ᶠ k in atTop, ∀ t ∈ Ioc (-1 : ℝ) 0, Q k t
  filter_upwards [hgood] with k hk t ht
  by_contra hQt
  have hbad : ∃ t ∈ Ioc (-1 : ℝ) 0, ¬ Q k t := ⟨t, ht, hQt⟩
  have hchosen : ¬ Q k (tau k) := by
    simpa only [tau, dif_pos hbad] using (Classical.choose_spec hbad).2
  exact hchosen hk

end M23TerminalMetricConvergence
end PoincareConjecture
