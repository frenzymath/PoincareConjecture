import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.CompactImageRegularity
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.EmbeddingInverse
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.RelativeCompactMetric
import Mathlib.Topology.MetricSpace.Thickening











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.M28.RegularPointedMetricConvergence

variable {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)] [∀ k, T2Space (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
  [∀ k, IsManifold (𝓡 3) ∞ (M k)]
  {g : ∀ k, RiemannianMetric 3 (M k)} {p : ∀ k, M k}





theorem exists_eventual_compact_stage_regularComponent
    (G : RegularPointedMetricConvergence g p) :
    letI := G.limitCarrier.topologicalSpace
    ∀ j : ℕ, ∃ delta : ℝ, 0 < delta ∧ ∀ᶠ k in atTop,
      G.embedding k '' closure (G.exhaustion j) ⊆
        regularComponent (g (G.subsequence k)) (p (G.subsequence k)) delta := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  let := G.limitCarrier.t2Space
  let := G.limitCarrier.t3Space
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 3) : G.limitCarrier.carrier → Type _) :=
    ⟨G.limitMetric.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : G.limitCarrier.carrier → Type _) :=
    ⟨⟨G.limitMetric.inner, G.limitMetric.toContinuousRiemannianMetric.continuous,
      fun _ _ _ => rfl⟩⟩
  let : EMetricSpace G.limitCarrier.carrier :=
    EMetricSpace.ofRiemannianMetric (𝓡 3) G.limitCarrier.carrier
  intro j
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ
    (fun i => subset_closure.trans (G.exhaustion_step i))
  obtain ⟨r, hr, hthick⟩ := (G.exhaustion_compactClosure j).exists_thickening_subset_open
    (G.exhaustion_open (j + 1)) (G.exhaustion_step j)
  let delta := r / 4
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  refine ⟨delta, hdelta, ?_⟩
  filter_upwards [G.eventually_compact_relative_inner_bounds
    (closure (G.exhaustion (j + 2))) (G.exhaustion_compactClosure (j + 2)) 1
      (by norm_num), eventually_ge_atTop (j + 3)] with k hk hjk
  let e := G.stageDiffeomorph k
  let V : TopologicalSpace.Opens G.limitCarrier.carrier :=
    ⟨G.exhaustion (j + 2), G.exhaustion_open (j + 2)⟩
  have hVs : closure (V : Set G.limitCarrier.carrier) ⊆ e.source :=
    (G.exhaustion_step (j + 2)).trans (hmono hjk)
  have hsmall : closure (G.exhaustion j) ⊆ (V : Set G.limitCarrier.carrier) :=
    (G.exhaustion_step j).trans (hmono (by omega))
  have hreg : G.embedding k '' closure (G.exhaustion j) ⊆
      regularPoints (g (G.subsequence k)) delta := by
    rintro _ ⟨x, hx, rfl⟩
    refine mem_regularPoints_of_compact_inverse_buffer G.limitMetric (g (G.subsequence k))
      e V (G.exhaustion_compactClosure (j + 2)) hVs
      (G.exhaustion_compactClosure (j + 1)) (G.exhaustion_step (j + 1))
      ?_ (hsmall hx) hdelta ?_
    · intro z hz v
      have hb := (hk z (subset_closure hz) v).1
      have hn : 0 ≤ G.limitMetric.inner z v v := by
        by_cases hv : v = 0
        · subst v
          simp +instances only [map_zero, le_refl]
        · exact (G.limitMetric.pos z v hv).le
      change G.limitMetric.inner z v v ≤ 4 * (g (G.subsequence k)).inner
        (G.embedding k z) (mfderiv (𝓡 3) (𝓡 3) (G.embedding k) z v)
        (mfderiv (𝓡 3) (𝓡 3) (G.embedding k) z v)
      norm_num at hb
      linarith
    · intro z hz
      apply subset_closure
      apply hthick
      apply (Metric.mem_thickening_iff_exists_edist_lt _ _).mpr
      refine ⟨x, hx, ?_⟩
      change edist x z < ENNReal.ofReal (2 * delta) at hz
      rw [edist_comm]
      exact hz.trans_le (ENNReal.ofReal_le_ofReal (by dsimp [delta]; linarith))
  have hcont : ContinuousOn (G.embedding k) (closure (G.exhaustion j)) :=
    e.contMDiffOn.continuousOn.mono (hsmall.trans (subset_closure.trans hVs))
  have hconnected := (G.exhaustion_connected j).isPreconnected.closure.image
    (G.embedding k) hcont
  have hbase : p (G.subsequence k) ∈ G.embedding k '' closure (G.exhaustion j) :=
    ⟨G.base, subset_closure (G.base_in_exhaustion j), G.base_preserving k⟩
  exact hconnected.subset_connectedComponentIn hbase hreg

end PoincareConjecture.M28.RegularPointedMetricConvergence
