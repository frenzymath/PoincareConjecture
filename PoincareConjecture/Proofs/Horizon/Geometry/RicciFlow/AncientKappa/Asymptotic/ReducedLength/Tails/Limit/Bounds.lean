import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Mass.Distortion
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Tails.VolumeBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.AncientCompactTimeConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.secondCountable

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} {S : AncientRescalingSequence K}
  (G : AncientCompactTimeConvergence S)

theorem eventually_limit_base_distance_le_twice_source {t : ℝ} (ht : t < 0)
    (x : G.limit.carrier.carrier) :
    ∀ᶠ k in atTop,
      ((G.limit.flow.metric t).edist G.limit.base x).toReal ≤
        2 * (((S.rescaling (G.subsequence k)).flow.metric t).edist
          (S.base (G.subsequence k)) (G.sourcePoint k x)).toReal := by
  let g := G.limit.flow.metric t
  let d := (g.edist G.limit.base x).toReal
  let : PreconnectedSpace G.limit.carrier.carrier :=
    ⟨G.limit.carrier.connected.isPreconnected⟩
  by_cases hd : d = 0
  · exact Filter.Eventually.of_forall fun k => by
      change d ≤ _
      rw [hd]
      positivity
  have hdpos : 0 < d := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hd)
  have hc := g.isCompact_closure_ball_of_metricComplete
    (G.limit.complete t ht) G.limit.base d
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hc
  have hxcover : x ∈ ⋃ j, G.exhaustion j := by rw [G.exhaustion_covers]; trivial
  obtain ⟨j', hj'⟩ := mem_iUnion.mp hxcover
  filter_upwards [G.eventually_source_base_ball_subset_sourcePoint_image_ball ht
    (show 0 < d / 2 by positivity) (by norm_num : (1 : ℝ) < 2),
    eventually_timeWindow_mem_nhds ht, eventually_ge_atTop j,
    eventually_ge_atTop j'] with k hball hkt hjk hjk'
  let h := (S.rescaling (G.subsequence k)).flow.metric t
  change d ≤ 2 * (h.edist (S.base (G.subsequence k)) (G.sourcePoint k x)).toReal
  by_contra hbad
  have hnear : G.sourcePoint k x ∈ h.ball (S.base (G.subsequence k)) (d / 2) := by
    apply (ENNReal.lt_ofReal_iff_toReal_lt
      (h.edist_ne_top (S.base (G.subsequence k)) (G.sourcePoint k x))).mpr
    linarith
  obtain ⟨y, hy, hxy⟩ := hball hnear
  have hyball : y ∈ g.ball G.limit.base d := by
    simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hy
  have hyexh : y ∈ G.exhaustion k :=
    G.exhaustion_monotone hjk (hj (subset_closure hyball))
  have hxexh : x ∈ G.exhaustion k := G.exhaustion_monotone hjk' hj'
  let e := (G.embedding k).spatialHomeomorph (G.exhaustion_open k) hkt
  have hyx : y = x := e.injOn hyexh hxexh (by
    change ((G.embedding k).toFun (t, y)).2 = ((G.embedding k).toFun (t, x)).2
    rw [← G.sourcePoint_eq_at k (mem_of_mem_nhds hkt) hyexh,
      ← G.sourcePoint_eq_at k (mem_of_mem_nhds hkt) hxexh]
    exact hxy)
  subst y
  have hlt : d < d := (ENNReal.lt_ofReal_iff_toReal_lt
    (g.edist_ne_top G.limit.base x)).mp hyball
  exact (lt_irrefl d) hlt

theorem reducedLengthPullback_limit_lower_bound
    (P : AncientAsymptoticSolitonPredecessors K)
    {l : G.limit.carrier.carrier × ℝ → ℝ}
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback k z.1 z.2) l atTop (univ ×ˢ Ioi (0 : ℝ)))
    {τ : ℝ} (hτ : 0 < τ) (x : G.limit.carrier.carrier) :
    ((G.limit.flow.metric (-τ)).edist G.limit.base x).toReal ^ 2 /
        (4 * (16 * (2 * (n : ℝ) + 604) ^ 2 * τ)) -
          (n : ℝ) / 2 * max (τ ^ 2) (τ ^ 2)⁻¹ - 1 ≤ l (x, τ) := by
  apply le_of_tendsto_of_tendsto tendsto_const_nhds
    (hlim.tendsto_at (show (x, τ) ∈ univ ×ˢ Ioi (0 : ℝ) from ⟨mem_univ x, hτ⟩))
  filter_upwards [G.eventually_limit_base_distance_le_twice_source
    (neg_neg_of_pos hτ) x] with k hk
  have hsource := S.reducedLength_rescaled_lower_bound P (G.subsequence k) hτ
    (G.sourcePoint k x)
  let d := ((G.limit.flow.metric (-τ)).edist G.limit.base x).toReal
  let D := (((S.rescaling (G.subsequence k)).flow.metric (-τ)).edist
    (S.base (G.subsequence k)) (G.sourcePoint k x)).toReal
  let A := 16 * (2 * (n : ℝ) + 604) ^ 2 * τ
  have hA : 0 < A := by dsimp [A]; positivity
  have hsq : d ^ 2 ≤ 4 * D ^ 2 := by
    have h := (sq_le_sq₀ (show 0 ≤ d from ENNReal.toReal_nonneg)
      (show 0 ≤ 2 * D by dsimp [D]; positivity)).mpr hk
    nlinarith
  have hdist : d ^ 2 / (4 * A) ≤ D ^ 2 / A := by
    apply (div_le_div_iff₀ (by positivity : 0 < 4 * A) hA).mpr
    nlinarith [mul_le_mul_of_nonneg_right hsq hA.le]
  change d ^ 2 / (4 * A) - _ - 1 ≤ _
  exact (sub_le_sub_right (sub_le_sub_right hdist _) 1).trans hsource

theorem limit_ball_volume_le_euclidean
    (P : AncientAsymptoticSolitonPredecessors K) {τ : ℝ} (hτ : 0 < τ)
    (p : G.limit.carrier.carrier) {r : ℝ} (hr : 0 < r) :
    calibratedMetricVolume (G.limit.flow.metric (-τ))
        ((G.limit.flow.metric (-τ)).ball p r) ≤
      ENNReal.ofReal (RiemannianMetric.euclideanUnitBallVolume n * r ^ n) := by
  apply le_of_tendsto (G.tendsto_calibratedMetricVolume_ball (neg_neg_of_pos hτ) p hr)
  exact Filter.Eventually.of_forall fun k =>
    S.rescaled_ball_volume_le_euclidean P (G.subsequence k) hτ
      ((G.embedding k).toFun (-τ, p)).2 hr

end PoincareConjecture.AncientCompactTimeConvergence
