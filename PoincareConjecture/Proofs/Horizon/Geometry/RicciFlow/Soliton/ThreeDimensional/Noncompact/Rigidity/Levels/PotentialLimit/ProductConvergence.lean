import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.PotentialLimit
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.CompactConvergence

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.ShrinkingSolitonFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space
attribute [local instance] RicciFlow.smallCarrier RicciFlow.smallChartedSpace
  RicciFlow.smallIsManifold

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {S : GradientShrinkingSolitonData 3 M} (G : ShrinkingSolitonFlow S) {q : ℕ → M}
  (L : AncientPointedGeometricConvergence
    (fun _ => AncientRescalingSequence.smallRescalingCarrier (M := M))
    (fun _ => G.unscaledSourceFlow.shrink.metric)
    (fun k => equivShrink M (q k)) 1)

theorem NormalizedPotentialLimit.eventually_compact_domain
    (B : G.NormalizedPotentialLimit L) (K : Set L.limitCarrier.carrier)
    (hK : IsCompact K) :
    ∀ᶠ k in atTop, K ⊆ L.exhaustion (B.subsequence k) := by
  exact B.subsequence_strictMono.tendsto_atTop.eventually
    ((G.unscaledOriginalEmbedding_tangentNorm_eventually_le L K hK).mono
      fun _ hk => hk.1)

theorem NormalizedPotentialLimit.eventually_compact_C1_error
    (B : G.NormalizedPotentialLimit L) (K : Set L.limitCarrier.carrier)
    (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ k in atTop, ∀ x ∈ K,
      |G.normalizedPotentialPullback L (B.subsequence k) x - B.potential x| ≤ δ ∧
      ∀ v : TangentSpace (𝓡 3) x,
        |mvfderiv (𝓡 3) (G.normalizedPotentialPullback L (B.subsequence k)) x v -
          mvfderiv (𝓡 3) B.potential x v| ≤
            δ * (L.limitFlow.metric 0).tangentNorm x v := by
  apply RiemannianMetric.eventually_uniform_value_differential_error_of_chart_jets
    (L.limitFlow.metric 0) B.potential_contMDiff ?_ B.potential_jets_tendsto K hK hδ
  intro A hA
  filter_upwards [B.eventually_compact_domain G L A hA] with k hk x hx
  exact ((G.normalizedPotentialPullback_contMDiffOn L (B.subsequence k)).contMDiffAt
    ((L.exhaustion_open _).mem_nhds (hk hx))).mdifferentiableAt (by simp)

variable {N : Type*} [TopologicalSpace N] [CompactSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N] [IsManifold (𝓡 2) ∞ N]

omit [IsManifold (𝓡 2) ∞ N] in
theorem NormalizedPotentialLimit.eventually_product_slab_domain
    (B : G.NormalizedPotentialLimit L)
    (e : N × ℝ → L.limitCarrier.carrier)
    (he : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ e) (r : ℝ) :
    ∀ᶠ k in atTop, ∀ y s, s ∈ Icc (-r) r →
      e (y, s) ∈ L.exhaustion (B.subsequence k) := by
  have hK : IsCompact (e '' (univ ×ˢ Icc (-r) r)) :=
    (isCompact_univ.prod isCompact_Icc).image he.continuous
  filter_upwards [B.eventually_compact_domain G L _ hK] with k hk y s hs
  exact hk ⟨(y, s), ⟨mem_univ _, hs⟩, rfl⟩

theorem NormalizedPotentialLimit.eventually_product_slab_C1_error
    (B : G.NormalizedPotentialLimit L) (h : RiemannianMetric 2 N)
    (e : N × ℝ → L.limitCarrier.carrier)
    (he : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ e)
    (hpotential : ∀ z, B.potential (e z) = z.2)
    (hmetric : ∀ (z : N × ℝ)
      (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
      (L.limitFlow.metric 0).inner (e z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
        h.inner z.1 v.1 w.1 + v.2 * w.2)
    (r : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ k in atTop, ∀ y s, s ∈ Icc (-r) r →
      |G.normalizedPotentialPullback L (B.subsequence k) (e (y, s)) - s| ≤ δ ∧
      |deriv (fun t => G.normalizedPotentialPullback L (B.subsequence k) (e (y, t))) s - 1| ≤ δ ∧
      ∀ v : TangentSpace (𝓡 2) y,
        |mvfderiv (𝓡 2)
          (fun z => G.normalizedPotentialPullback L (B.subsequence k) (e (z, s))) y v| ≤
          δ * h.tangentNorm y v := by
  let K := e '' (univ ×ˢ Icc (-r) r)
  have hK : IsCompact K := (isCompact_univ.prod isCompact_Icc).image he.continuous
  filter_upwards [B.eventually_compact_C1_error G L K hK hδ,
    B.eventually_product_slab_domain G L e he r] with k hk hdomain y s hs
  have hys : e (y, s) ∈ K := ⟨(y, s), ⟨mem_univ _, hs⟩, rfl⟩
  have hf := ((G.normalizedPotentialPullback_contMDiffOn L (B.subsequence k)).contMDiffAt
    ((L.exhaustion_open _).mem_nhds (hdomain y s hs))).mdifferentiableAt (by simp)
  have hb := B.potential_contMDiff.mdifferentiable (by simp) (e (y, s))
  have he' := he.mdifferentiable (by simp) (y, s)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hpotential] using (hk (e (y, s)) hys).1
  · have herr := (hk (e (y, s)) hys).2
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e (y, s) (0, 1))
    rw [← RiemannianMetric.mvfderiv_product_comp_vertical hf he',
      ← RiemannianMetric.mvfderiv_product_comp_vertical hb he'] at herr
    have hn : (L.limitFlow.metric 0).tangentNorm (e (y, s))
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e (y, s) (0, 1)) = 1 := by
      simp only [RiemannianMetric.tangentNorm, hmetric, map_zero, zero_add,
        one_mul, Real.sqrt_one]
    simpa only [hpotential, deriv_id'', hn, mul_one] using herr
  · intro v
    have herr := (hk (e (y, s)) hys).2
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e (y, s) (v, 0))
    rw [← RiemannianMetric.mvfderiv_product_comp_horizontal hf he' v,
      ← RiemannianMetric.mvfderiv_product_comp_horizontal hb he' v] at herr
    have hn : (L.limitFlow.metric 0).tangentNorm (e (y, s))
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e (y, s) (v, 0)) =
        h.tangentNorm y v := by
      simp only [RiemannianMetric.tangentNorm, hmetric, mul_zero, add_zero]
    have hbconst : (fun z => B.potential (e (z, s))) = (fun _ : N => s) :=
      funext fun z => hpotential (z, s)
    rw [hbconst] at herr
    simpa [mvfderiv, hn] using herr

end PoincareConjecture.ShrinkingSolitonFlow
