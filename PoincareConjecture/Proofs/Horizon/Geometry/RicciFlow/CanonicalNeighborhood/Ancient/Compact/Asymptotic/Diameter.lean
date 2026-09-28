import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Inheritance.Volume
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Diameter.Bounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.AncientCompactTimeConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t3Space FlowCarrier.secondCountable

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {S : AncientRescalingSequence K}
  (G : AncientCompactTimeConvergence S)

theorem tendsto_metricDiameter_of_noncompact_limit
    (hcompact : IsCompact (univ : Set M))
    (hnoncompact : ¬ IsCompact (univ : Set G.limit.carrier.carrier))
    {t : ℝ} (ht : t < 0) :
    Tendsto (fun k ↦ metricDiameter
      ((S.rescaling (G.subsequence k)).flow.metric t) univ) atTop atTop := by
  apply tendsto_atTop.mpr
  intro B
  let r := max B 0 + 1
  have hr : 0 < r := by dsimp [r]; positivity
  have hBr : B < r := by dsimp [r]; linarith [le_max_left B 0]
  let g := G.limit.flow.metric t
  have hball : IsCompact (closure (g.ball G.limit.base (2 * r))) :=
    g.isCompact_closure_ball_of_metricComplete (G.limit.complete t ht) G.limit.base (2 * r)
  obtain ⟨q, hq⟩ : ∃ q, q ∉ closure (g.ball G.limit.base (2 * r)) := by
    by_contra hall
    push Not at hall
    apply hnoncompact
    rwa [Set.eq_univ_iff_forall.mpr hall] at hball
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset (hball.insert q)
  filter_upwards [G.eventually_source_ball_subset_image_ball ht G.limit.base hr
      (show (1 : ℝ) < 2 by norm_num),
    eventually_timeWindow_mem_nhds ht, eventually_ge_atTop j] with k hcover htime hjk
  by_contra hdiam
  have hdiamlt : metricDiameter ((S.rescaling (G.subsequence k)).flow.metric t) univ < r :=
    (lt_of_not_ge hdiam).trans hBr
  have hsource := compact_mem_ball_of_metricDiameter_lt
    ((S.rescaling (G.subsequence k)).flow.metric t) hcompact hdiamlt
    ((G.embedding k).toFun (t, G.limit.base)).2 ((G.embedding k).toFun (t, q)).2
  obtain ⟨x, hx, heq⟩ := hcover hsource
  have hdomain : insert q (closure (g.ball G.limit.base (2 * r))) ⊆ G.exhaustion k :=
    hj.trans (G.exhaustion_monotone hjk)
  have hxk : x ∈ G.exhaustion k := hdomain (mem_insert_of_mem q (subset_closure hx))
  have hqk : q ∈ G.exhaustion k := hdomain (mem_insert q _)
  have hpair : (G.embedding k).toFun (t, x) = (G.embedding k).toFun (t, q) :=
    Prod.ext (((G.embedding k).time_preserving t x).trans
      ((G.embedding k).time_preserving t q).symm) heq
  have hxq : x = q := congrArg Prod.snd ((G.embedding k).injective_on
    ⟨mem_of_mem_nhds htime, hxk⟩ ⟨mem_of_mem_nhds htime, hqk⟩ hpair)
  exact hq (hxq ▸ subset_closure hx)

theorem tendsto_metricDiameter_neg_one_of_noncompact_limit
    (hcompact : IsCompact (univ : Set M))
    (hnoncompact : ¬ IsCompact (univ : Set G.limit.carrier.carrier)) :
    Tendsto (fun k ↦ metricDiameter
      ((S.rescaling (G.subsequence k)).flow.metric (-1)) univ) atTop atTop :=
  G.tendsto_metricDiameter_of_noncompact_limit hcompact hnoncompact (by norm_num)

end PoincareConjecture.AncientCompactTimeConvergence
