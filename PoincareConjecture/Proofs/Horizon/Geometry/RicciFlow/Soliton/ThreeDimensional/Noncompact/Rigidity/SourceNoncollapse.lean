import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Limit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.SpatialLimit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.RescaledSlice







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

namespace RicciFlow

attribute [local instance] smallCarrier smallChartedSpace smallIsManifold
  smallMeasurableSpace smallBorelSpace smallT3Space

omit [T2Space M] [ConnectedSpace M] in
theorem metricKappaNoncollapsed_shrink {J : Set ℝ} (F : RicciFlow n M J)
    (t : ℝ) {κ : ℝ} (hκ : MetricKappaNoncollapsed (F.metric t) (F.connection t) κ) :
    MetricKappaNoncollapsed (F.shrink.metric t) (F.shrink.connection t) κ := by
  refine ⟨hκ.1, fun p r hr hbound => ?_⟩
  rw [calibratedMetricVolume_eq_volumeMeasure, F.shrink_volumeMeasure_ball,
    ← calibratedMetricVolume_eq_volumeMeasure]
  apply hκ.2 ((equivShrink M).symm p) r hr
  intro q hq
  have hmem : equivShrink M q ∈ (F.shrink.metric t).ball p r := by
    simpa only [RiemannianMetric.ball, mem_ofPred_eq, F.shrink_edist,
      Equiv.symm_apply_apply] using hq
  simpa only [F.shrink_curvatureTensorNorm, Equiv.symm_apply_apply] using
    hbound (equivShrink M q) hmem

theorem interiorAncientRescaleAt_metricKappaNoncollapsed (F : RicciFlow n M (Iic 0))
    {κ : ℝ} (hκ : ∀ t ≤ 0, MetricKappaNoncollapsed (F.metric t) (F.connection t) κ)
    (Q : ℝ) (hQ : 0 < Q) (t₀ t : ℝ) (ht : t < -t₀ * Q) :
    MetricKappaNoncollapsed ((F.interiorAncientRescaleAt Q hQ t₀).metric t)
      ((F.interiorAncientRescaleAt Q hQ t₀).connection t) κ := by
  have htime : t₀ + t / Q ≤ 0 := by
    have h := (div_lt_iff₀ hQ).mpr ht
    linarith
  exact (hκ _ htime).rescaledMetric Q hQ

end RicciFlow

variable {N : Type u} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
  [MeasurableSpace N] [BorelSpace N] [T2Space N] [T3Space N]
  [SecondCountableTopology N] [ConnectedSpace N]

namespace ShrinkingSolitonFlow

variable {S : GradientShrinkingSolitonData 3 N} (G : ShrinkingSolitonFlow S)

theorem ancientSourceFlow_metricKappaNoncollapsed (t : ℝ) (ht : t ≤ 0) :
    MetricKappaNoncollapsed (G.ancientSourceFlow.metric t)
      (G.ancientSourceFlow.connection t) S.kappa := by
  obtain ⟨E⟩ := G.self_similar (t + -1) (by linarith)
  exact E.kappaNoncollapsed (abs_pos.mpr (by linarith)) S.connection
    (G.flow.connection (t + -1)) S.kappa_noncollapsed

end ShrinkingSolitonFlow

end PoincareConjecture
