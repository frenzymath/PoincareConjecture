import PoincareLib.Geometry.Spacetime.Rescaling.Interval
import PoincareLib.Geometry.Riemannian.Homothety.Calculus
import PoincareLib.Geometry.RicciFlow.Generalized.Gauge.Geometry

/-! Ported from Mapher06/Poincare-MorganTian, `PoincareMT/Definitions/M13OrdinaryRescaling.lean`,
revision `49331b7d7ecad38f53e4300c3b35d6a84b2cc648`.
Declaration bodies are unchanged; only imports and module placement differ. -/

/-!
# Ordinary parabolic rescaling and its selected product geometries

Morgan-Tian Definitions 3.1-3.2, p. 35, Definition 3.40 and the
time-translation paragraph, p. 61. The rescaled ordinary flow has the exact
affine image interval and the metric Q*g(a+s/Q) at every real s. Its
existence is an M13 theorem output, including for an empty spatial manifold.
The separate nonempty product comparison uses the supplied source and
target M12 product witnesses and their actual manifold differentials.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {I : SpacetimeInterval}

/-- An actual ordinary flow on the affine image interval. The identity of
metric representatives holds at all real times; the flow's smoothness and
Ricci equation concern precisely its specified interval. -/
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

/-- The prescribed target-to-source point map between the exact products. -/
noncomputable def ordinaryProductTimeMap (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (I : SpacetimeInterval) : (parabolicInterval Q hQ a I).domain × M → I.domain × M :=
  fun p ↦ (parabolicTimePointInv Q hQ a I p.1, p.2)

/-- The actual comparison of two fixed M12 ordinary-product witnesses.
The map reverses the affine clock and keeps the spatial point. Its horizontal
equivalence is the restriction of that same map's actual differential. -/
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

end PoincareMT
