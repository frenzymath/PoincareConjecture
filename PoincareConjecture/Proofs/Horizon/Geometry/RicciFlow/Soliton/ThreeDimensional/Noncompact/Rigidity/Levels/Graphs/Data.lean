import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.Graphs.Embeddings
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.Graph.Metric


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

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
  (B : G.NormalizedPotentialLimit L)
  {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N] [IsManifold (𝓡 2) ∞ N]


def potentialLevelGraphMap
    (e : (N × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ L.limitCarrier.carrier)
    (u : N → ℝ) (k : ℕ) (y : N) : M :=
  G.unscaledOriginalEmbedding L (B.subsequence k) (e (y, u y))

variable [T3Space N] [MeasurableSpace N] [BorelSpace N]



structure PotentialLevelGraphs
    (h : RiemannianMetric 2 N)
    (e : (N × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ L.limitCarrier.carrier)
    (base : N) where
  offset : ℕ
  height : ℕ → N → ℝ
  height_contMDiff : ∀ k, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (height k)
  height_mem : ∀ k y, height k y ∈ Ioo (-1) 1
  height_base : ∀ k, height k base = 0
  graph_mem : ∀ k y, e (y, height k y) ∈ L.exhaustion (B.subsequence (k + offset))
  graph_level : ∀ k y,
    S.potential (G.potentialLevelGraphMap L B e (height k) (k + offset) y) =
      S.potential (q (L.subsequence (B.subsequence (k + offset))))
  graph_contMDiff : ∀ k, ContMDiff (𝓡 2) (𝓡 3) ∞
    (G.potentialLevelGraphMap L B e (height k) (k + offset))
  graph_injective : ∀ k, Injective (G.potentialLevelGraphMap L B e (height k) (k + offset))
  graph_immersion : ∀ k y, Injective (mfderiv (𝓡 2) (𝓡 3)
    (G.potentialLevelGraphMap L B e (height k) (k + offset)) y)
  metric : ℕ → RiemannianMetric 2 N
  metric_inner : ∀ k y (v w : TangentSpace (𝓡 2) y),
    (metric k).inner y v w =
      S.metric.inner (G.potentialLevelGraphMap L B e (height k) (k + offset) y)
        (mfderiv (𝓡 2) (𝓡 3) (G.potentialLevelGraphMap L B e (height k) (k + offset)) y v)
        (mfderiv (𝓡 2) (𝓡 3) (G.potentialLevelGraphMap L B e (height k) (k + offset)) y w)
  height_tendsto_C1 : ∀ δ > 0, ∀ᶠ k in atTop,
    (∀ y, |height k y| ≤ δ) ∧ ∀ y (v : TangentSpace (𝓡 2) y),
      |mvfderiv (𝓡 2) (height k) y v| ≤ δ * h.tangentNorm y v
  area_tendsto : Tendsto (fun k => (metric k).volumeMeasure.real univ) atTop
    (𝓝 (h.volumeMeasure.real univ))

namespace PotentialLevelGraphs

variable {G L B} {h : RiemannianMetric 2 N}
  {e : (N × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ L.limitCarrier.carrier}
  {base : N} (A : G.PotentialLevelGraphs L B h e base)

def map (k : ℕ) : N → M :=
  G.potentialLevelGraphMap L B e (A.height k) (k + A.offset)

theorem map_base (hebase : e (base, 0) = L.base) (k : ℕ) :
    A.map k base = q (L.subsequence (B.subsequence (k + A.offset))) := by
  change G.unscaledOriginalEmbedding L (B.subsequence (k + A.offset))
    (e (base, A.height k base)) = _
  rw [A.height_base, hebase, G.unscaledOriginalEmbedding_base]

theorem range_isCompact [CompactSpace N] (k : ℕ) : IsCompact (range (A.map k)) :=
  isCompact_range (A.graph_contMDiff k).continuous

end PotentialLevelGraphs

end PoincareConjecture.ShrinkingSolitonFlow
