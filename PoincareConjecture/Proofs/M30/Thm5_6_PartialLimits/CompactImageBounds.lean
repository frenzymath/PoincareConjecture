import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.MetricComparison
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.SourceMetric
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.PathComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompleteBalls










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30.PartialPointedMetricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space

variable {n : ℕ} {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
  [∀ k, IsManifold (𝓡 n) ∞ (M k)]
  {g : ∀ k, RiemannianMetric n (M k)} {p : ∀ k, M k} {A : ℝ}
  (G : PartialPointedMetricConvergence g p A)



theorem eventually_image_ball_subset_double {r : ℝ}
    (hcompact : IsCompact (closure (G.limitMetric.ball G.base r))) :
    ∀ᶠ k in atTop,
      G.embedding k '' G.limitMetric.ball G.base r ⊆
        (g (G.subsequence k)).ball (p (G.subsequence k)) (2 * r) := by
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : G.limitCarrier.carrier → Type _) :=
    ⟨G.limitMetric.toRiemannianMetric⟩
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hcompact
  have hsqrt : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  filter_upwards [G.eventually_pullback_inner_le_twice hcompact,
    eventually_ge_atTop j] with k hk hjk
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨γ, hγ0, hγ1, hγ, hlength, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hx zero_lt_one
  have hpath : MapsTo γ (Icc (0 : ℝ) 1) (G.limitMetric.ball G.base r) := by
    intro t ht
    exact ((Manifold.riemannianEDist_le_pathELength
      (hγ.contMDiffOn.mono (Icc_subset_Icc_right ht.2)) hγ0 rfl ht.1).trans
        (Manifold.pathELength_mono le_rfl ht.2)).trans_lt hlength
  have hmap (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ContMDiffAt (𝓡 n) (𝓡 n) 1 (G.embedding k) (γ t) :=
    ((G.embedding_smooth k
      ⟨γ t, G.exhaustion_monotone hjk (hj (subset_closure (hpath ht)))⟩).contMDiffAt).of_le
        (by simp)
  have hlength' := G.limitMetric.pathELength_comp_le_of_tangentNorm_le_on_Icc
    (g (G.subsequence k)) (by norm_num : (0 : ℝ) ≤ 2) hγ hmap (by
      intro t ht v
      change Real.sqrt _ ≤ 2 * Real.sqrt _
      calc
        _ ≤ Real.sqrt (2 * G.limitMetric.inner (γ t) v v) :=
          Real.sqrt_le_sqrt (hk (γ t) (subset_closure (hpath ht)) v)
        _ = Real.sqrt 2 * Real.sqrt (G.limitMetric.inner (γ t) v v) :=
          Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) _
        _ ≤ _ := mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg _))
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : M (G.subsequence k) → Type _) :=
    ⟨(g (G.subsequence k)).toRiemannianMetric⟩
  have hreg : ContMDiffOn 𝓘(ℝ) (𝓡 n) 1 (G.embedding k ∘ γ) (Icc 0 1) :=
    fun t ht => ((hmap t ht).comp t hγ.contMDiffAt).contMDiffWithinAt
  have hd : (g (G.subsequence k)).edist (p (G.subsequence k)) (G.embedding k x) ≤
      (g (G.subsequence k)).pathELength (G.embedding k ∘ γ) 0 1 :=
    Manifold.riemannianEDist_le_pathELength hreg
      (by simpa only [Function.comp_apply, hγ0] using G.base_preserving k)
      (by simp only [Function.comp_apply, hγ1]) zero_le_one
  change _ < ENNReal.ofReal (2 * r)
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  exact (hd.trans hlength').trans_lt
    (ENNReal.mul_lt_mul_right (by norm_num : ENNReal.ofReal (2 : ℝ) ≠ 0)
      ENNReal.ofReal_ne_top hlength)




theorem exists_eventually_compact_image_ball
    (hcomplete : G.limitCarrier.metricComplete G.limitMetric)
    {K : Set G.limitCarrier.carrier} (hK : IsCompact K) :
    ∃ R : ℝ, 0 < R ∧ ∀ᶠ k in atTop,
      G.embedding k '' K ⊆ (g (G.subsequence k)).ball (p (G.subsequence k)) R := by
  let : MetricSpace G.limitCarrier.carrier := G.limitCarrier.metricSpaceOf G.limitMetric
  obtain ⟨r, hr, hKr⟩ := hK.isBounded.subset_ball_lt 0 G.base
  have hKr' : K ⊆ G.limitMetric.ball G.base r := by
    simpa only [FlowCarrier.metricBall_eq_metricBallOf, FlowCarrier.metricBall] using hKr
  have hcompact : IsCompact (closure (G.limitMetric.ball G.base r)) := by
    apply IsCompact.of_isClosed_subset
      (G.limitMetric.isCompact_closedBall_of_metricComplete hcomplete G.base r) isClosed_closure
    apply closure_minimal
      (fun x (hx : G.limitMetric.edist G.base x < ENNReal.ofReal r) => hx.le)
    exact isClosed_le (continuous_const.edist continuous_id) continuous_const
  exact ⟨2 * r, by positivity, (G.eventually_image_ball_subset_double hcompact).mono
    fun _ hk => (image_mono hKr').trans hk⟩

end PoincareConjecture.M30.PartialPointedMetricConvergence
