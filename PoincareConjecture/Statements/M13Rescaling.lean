import PoincareConjecture.Definitions.M13Rescaling
import PoincareConjecture.Definitions.M13OrdinaryRescaling

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure GeneralizedParabolicRescalingTheory (n : ℕ) : Prop where
  rescale : ∀ (X : Type u) [TopologicalSpace X]
    (A : AdaptedMetricAtlas n X) (R : GeneralizedFlowCarrierConclusion A)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ), Nonempty (GeneralizedParabolicRescaling R Q hQ a)
  metric_homothety : ∀ (M N : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
    [T3Space M] [MeasurableSpace M] [BorelSpace M]
    [T3Space N] [MeasurableSpace N] [BorelSpace N]
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (Q : ℝ), 0 < Q →
    MetricHomothety g h f Q → MetricHomothetyCalculus g h f Q
  coordinate_metric_homothety : ∀ (M N : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
    [T3Space M] [MeasurableSpace M] [BorelSpace M]
    [T3Space N] [MeasurableSpace N] [BorelSpace N]
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (Q : ℝ), 0 < Q →
    MetricHomothety g h f Q → MetricHomothetyCalculus g h f Q
  ordinary_flow : ∀ (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [SecondCountableTopology M]
    (I : SpacetimeInterval) (F : RicciFlow n M I.domain) (Q : ℝ) (hQ : 0 < Q) (a : ℝ),
    Nonempty (OrdinaryParabolicRescaling F Q hQ a)
  ordinary_product_comparison : ∀ (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [Nonempty M]
    (I : SpacetimeInterval) (F : RicciFlow n M I.domain) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (R : OrdinaryParabolicRescaling F Q hQ a)
    (source : OrdinaryProductRicciGeometry F.metric I)
    (target : OrdinaryProductRicciGeometry R.flow.metric (parabolicInterval Q hQ a I)),
    Nonempty (OrdinaryParabolicProductComparison R source target)

end PoincareConjecture
