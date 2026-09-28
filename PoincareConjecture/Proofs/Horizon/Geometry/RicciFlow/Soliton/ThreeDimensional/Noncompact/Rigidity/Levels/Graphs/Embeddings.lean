import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.PotentialLimit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.MetricComparison


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter Function
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.ShrinkingSolitonFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space
attribute [local instance] RicciFlow.smallCarrier RicciFlow.smallChartedSpace
  RicciFlow.smallIsManifold

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {S : GradientShrinkingSolitonData 3 M} (G : ShrinkingSolitonFlow S) {q : ℕ → M}
  (L : AncientPointedGeometricConvergence
    (fun _ => AncientRescalingSequence.smallRescalingCarrier (M := M))
    (fun _ => G.unscaledSourceFlow.shrink.metric)
    (fun k => equivShrink M (q k)) 1)

theorem unscaledOriginalEmbedding_injOn (k : ℕ) :
    InjOn (G.unscaledOriginalEmbedding L k) (L.exhaustion k) := by
  intro x hx y hy hxy
  have hsmall : L.embedding k x = L.embedding k y :=
    (equivShrink M).symm.injective hxy
  have hh := (L.embedding_open k).injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hsmall
  exact congrArg Subtype.val hh

theorem unscaledOriginalEmbedding_isLocalDiffeomorphOn (k : ℕ) :
    IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞
      (G.unscaledOriginalEmbedding L k) (L.exhaustion k) := by
  intro x
  exact (L.embedding_smooth k x).comp (𝓡 3) M
    ((Poincare.Manifold.shrinkDiffeomorph (𝓡 3) M).symm.isLocalDiffeomorph _)



theorem unscaledOriginalEmbedding_eventually_relative_metric_error
    (K : Set L.limitCarrier.carrier) (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, K ⊆ L.exhaustion k ∧
      ∀ x ∈ K, ∀ v : TangentSpace (𝓡 3) x,
        |S.metric.inner (G.unscaledOriginalEmbedding L k x)
          (mfderiv (𝓡 3) (𝓡 3) (G.unscaledOriginalEmbedding L k) x v)
          (mfderiv (𝓡 3) (𝓡 3) (G.unscaledOriginalEmbedding L k) x v) -
            (L.limitFlow.metric 0).inner x v v| ≤
          ε * (L.limitFlow.metric 0).inner x v v := by
  let W := AncientPointedGeometricConvergence.window
    (C := fun _ => AncientRescalingSequence.smallRescalingCarrier (M := M))
    (J := fun _ => Iio (1 : ℝ)) (T := 1)
    (fun _ => G.unscaledSourceFlow.shrink) L
    (a := -1) (b := 1 / 2) (by norm_num) (by norm_num) 0
    (by intro k t ht; exact ht.2.trans (by norm_num : (1 / 2 : ℝ) < 1))
  obtain ⟨j, hj⟩ := W.exists_exhaustion_superset hK
  have hmono := monotone_nat_of_le_succ L.exhaustion_increasing
  filter_upwards [W.eventually_pullback_inner_bounds hK (by norm_num : (0 : ℝ) ∈ Ioo (-1) (1 / 2)) hε,
    eventually_ge_atTop j] with k hk hjk
  have hmem : K ⊆ L.exhaustion k := fun x hx => hmono hjk (hj hx)
  refine ⟨hmem, fun x hx v => ?_⟩
  have hh := hk x hx v
  change (1 - ε) * (L.limitFlow.metric 0).inner x v v ≤
      spatialPullbackInner L.limitCarrier
        (AncientRescalingSequence.smallRescalingCarrier (M := M))
        (G.unscaledSourceFlow.shrink.metric 0) (L.embedding k) x v v ∧
    spatialPullbackInner L.limitCarrier
        (AncientRescalingSequence.smallRescalingCarrier (M := M))
        (G.unscaledSourceFlow.shrink.metric 0) (L.embedding k) x v v ≤
      (1 + ε) * (L.limitFlow.metric 0).inner x v v at hh
  rw [← G.unscaledOriginalEmbedding_inner L k x (hmem hx) v v] at hh
  exact abs_le.mpr ⟨by linarith [hh.1], by linarith [hh.2]⟩

end PoincareConjecture.ShrinkingSolitonFlow
