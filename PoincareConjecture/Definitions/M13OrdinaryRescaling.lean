import PoincareConjecture.Definitions.M13IntervalGeometry
import PoincareConjecture.Statements.M13MetricHomothety
import PoincareConjecture.Statements.M12GeneralizedEquation

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {I : SpacetimeInterval}

structure OrdinaryParabolicRescaling (F : RicciFlow n M I.domain)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) where
  flow : RicciFlow n M (parabolicInterval Q hQ a I).domain
  metric_eq : ∀ (s : ℝ) (x : M) (u v : TangentSpace (𝓡 n) x),
    (flow.metric s).inner x u v = Q * (F.metric (parabolicTimeInv Q a s)).inner x u v
  metric_homothety : ∀ s : ℝ,
    MetricHomothety (F.metric (parabolicTimeInv Q a s)) (flow.metric s)
      (Diffeomorph.refl (𝓡 n) M ∞) Q
  metric_calculus : ∀ [T3Space M] [MeasurableSpace M] [BorelSpace M], ∀ s : ℝ,
    MetricHomothetyCalculus (F.metric (parabolicTimeInv Q a s)) (flow.metric s)
      (Diffeomorph.refl (𝓡 n) M ∞) Q

noncomputable def ordinaryProductTimeMap (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (I : SpacetimeInterval) : (parabolicInterval Q hQ a I).domain × M → I.domain × M :=
  fun p ↦ (parabolicTimePointInv Q hQ a I p.1, p.2)

structure OrdinaryParabolicProductComparison [Nonempty M]
    {F : RicciFlow n M I.domain} {Q : ℝ} {hQ : 0 < Q} {a : ℝ}
    (R : OrdinaryParabolicRescaling F Q hQ a)
    (source : OrdinaryProductRicciGeometry F.metric I)
    (target : OrdinaryProductRicciGeometry R.flow.metric (parabolicInterval Q hQ a I)) where
  source_equation : IntrinsicGeneralizedRicciEquation source.leafwiseConnection
  target_equation : IntrinsicGeneralizedRicciEquation target.leafwiseConnection
  comparison : Diffeomorph (spacetimeModel n) (spacetimeModel n)
    target.product.spacetime.Point source.product.spacetime.Point ∞
  comparison_eq : ∀ p : target.product.spacetime.Point,
    comparison p = ordinaryProductTimeMap Q hQ a I p
  coordinate_eq : ∀ p :
    (target.product.timeIntervals.interval (parabolicInterval Q hQ a I)).Point × M,
    comparison (target.product.productIdentification p) =
      source.product.productIdentification (ordinaryProductTimeMap Q hQ a I p)
  coordinate_derivative : ∀ (p :
    (target.product.timeIntervals.interval (parabolicInterval Q hQ a I)).Point × M)
    (b : ℝ) (u : TangentSpace (𝓡 n) p.2),
    mfderiv (spacetimeModel n) (spacetimeModel n) comparison
      (target.product.productIdentification p)
      (mfderiv (spacetimeModel n) (spacetimeModel n) target.product.productIdentification p
        (b • (target.product.timeIntervals.interval
          (parabolicInterval Q hQ a I)).positiveTangent p.1, u)) =
      mfderiv (spacetimeModel n) (spacetimeModel n) source.product.productIdentification
        (ordinaryProductTimeMap Q hQ a I p)
        ((b / Q) • (source.product.timeIntervals.interval I).positiveTangent
          (ordinaryProductTimeMap Q hQ a I p).1, u)
  time_vector_eq : ∀ p : target.product.spacetime.Point,
    mfderiv (spacetimeModel n) (spacetimeModel n) comparison p
      (target.product.spacetime.timeVector p) =
      (1 / Q : ℝ) • source.product.spacetime.timeVector (comparison p)
  horizontalTangentEquiv : ∀ p : target.product.spacetime.Point,
    target.product.spacetime.Horizontal p ≃L[ℝ]
      source.product.spacetime.Horizontal (comparison p)
  horizontalTangentEquiv_val : ∀ (p : target.product.spacetime.Point)
    (v : target.product.spacetime.Horizontal p),
    (horizontalTangentEquiv p v).val =
      mfderiv (spacetimeModel n) (spacetimeModel n) comparison p v.val
  horizontal_metric : ∀ (p : target.product.spacetime.Point)
    (u v : target.product.spacetime.Horizontal p),
    target.product.spacetime.horizontalMetric.inner p u v =
      Q * source.product.spacetime.horizontalMetric.inner (comparison p)
        (horizontalTangentEquiv p u) (horizontalTangentEquiv p v)

end PoincareConjecture
