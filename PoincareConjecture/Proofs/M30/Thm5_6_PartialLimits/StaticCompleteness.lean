import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.CompactBalls
import PoincareConjecture.Proofs.M07.Topology.MetricSpace.Completeness










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M30.PartialPointedMetricConvergence



theorem metricComplete_of_source_ball_coverage
    {n : ℕ} {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {g : ∀ k, RiemannianMetric n (M k)} {p : ∀ k, M k} {A : ℝ}
    (G : PartialPointedMetricConvergence g p A)
    (hcover : ∀ R : ℝ, 0 < R → ∃ l : ℕ, ∀ᶠ k in atTop,
      (g (G.subsequence k)).ball (p (G.subsequence k)) R ⊆
        G.embedding k '' G.exhaustion l) :
    G.limitCarrier.metricComplete G.limitMetric := by
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
    G.limitCarrier.chartedSpace
  let : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
  let : EMetricSpace G.limitCarrier.carrier :=
    G.limitCarrier.metricEMetricSpace G.limitMetric
  let : PreconnectedSpace G.limitCarrier.carrier :=
    FlowCarrier.preconnected_metricEMetricSpace G.limitCarrier G.limitMetric
  have hcompact (R : ℝ) (hR : 0 < R) :
      IsCompact (closure (G.limitMetric.ball G.base R)) := by
    obtain ⟨l, hl⟩ := hcover (2 * R) (by positivity)
    exact (G.exhaustion_compactClosure l).of_isClosed_subset isClosed_closure
      (closure_mono (G.ball_subset_exhaustion_of_source_ball_coverage hl))
  change CompleteSpace G.limitCarrier.carrier
  apply EMetric.complete_of_cauchySeq_tendsto
  intro s hs
  obtain ⟨N, hN⟩ := EMetric.cauchySeq_iff'.mp hs 1 zero_lt_one
  let d := edist (s N) G.base
  have hd : d ≠ ⊤ := Poincare.edist_ne_top_of_preconnected _ _
  let R : ℝ := d.toReal + 2
  have hR : 0 < R := by dsimp [R]; positivity
  have htail : ∀ᶠ k in atTop, s k ∈ closure (G.limitMetric.ball G.base R) := by
    filter_upwards [eventually_ge_atTop N] with k hk
    apply subset_closure
    change edist G.base (s k) < ENNReal.ofReal R
    rw [edist_comm]
    calc
      edist (s k) G.base ≤ edist (s k) (s N) + d := edist_triangle _ _ _
      _ < 1 + d := ENNReal.add_lt_add_right hd (hN k hk)
      _ ≤ ENNReal.ofReal R := by
        dsimp [R]
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by norm_num),
          ENNReal.ofReal_toReal hd]
        norm_num
        simpa only [add_comm d] using
          add_le_add_left (by norm_num : (1 : ℝ≥0∞) ≤ 2) d
  obtain ⟨x, _, hx⟩ := (hcompact R hR).isComplete (map s atTop) hs
    (le_principal_iff.mpr htail)
  exact ⟨x, hx⟩

end PoincareConjecture.M30.PartialPointedMetricConvergence
