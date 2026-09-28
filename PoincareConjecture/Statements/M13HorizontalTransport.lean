import PoincareConjecture.Definitions.M13HorizontalTransport
import PoincareConjecture.Statements.M12HorizontalTheory
import PoincareConjecture.Statements.M13MetricHomothety

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {A : AdaptedMetricAtlas n X} {R : GeneralizedFlowCarrierConclusion A}
  {Q : ℝ} {hQ : 0 < Q} {a : ℝ}

structure ParabolicHorizontalCalculus (P : ParabolicSpacetimeRescaling R Q hQ a) : Prop where
  source_connections : Nonempty (LeafwiseLeviCivitaFamily R.spacetime R.slices)
  target_connections : Nonempty
    (LeafwiseLeviCivitaFamily P.realization.spacetime P.realization.slices)
  source_calculus : ∀ D : LeafwiseLeviCivitaFamily R.spacetime R.slices,
    HorizontalRicciCalculus D
  target_calculus : ∀ D : LeafwiseLeviCivitaFamily
    P.realization.spacetime P.realization.slices, HorizontalRicciCalculus D
  slice_calculus : ∀ t : ℝ,
    MetricHomothetyCalculus (R.slices t).metricOnPoints
      (P.realization.slices (parabolicTime Q a t)).metricOnPoints
      (P.sliceIdentification t) Q
  normalized_isometry : Nonempty (ParabolicNormalizedHorizontalIsometry P)
  section_smooth_iff : ∀ (V : HorizontalSection R.spacetime) (U : Set R.spacetime.Point),
    IsSmoothHorizontalSectionOn P.realization.spacetime (parabolicHorizontalSection P V) U ↔
      IsSmoothHorizontalSectionOn R.spacetime V U
  lie_eq : ∀ (p : R.spacetime.Point) (v w : R.spacetime.Horizontal p),
    horizontalMetricLieDerivative P.realization.spacetime p
      (P.horizontal p v) (P.horizontal p w) =
      horizontalMetricLieDerivative R.spacetime p v w
  riemann_eq : ∀ (D : LeafwiseLeviCivitaFamily R.spacetime R.slices)
    (D' : LeafwiseLeviCivitaFamily P.realization.spacetime P.realization.slices)
    (p : R.spacetime.Point) (v w z q : R.spacetime.Horizontal p),
    horizontalRiemann D' p (P.horizontal p v) (P.horizontal p w)
      (P.horizontal p z) (P.horizontal p q) = Q * horizontalRiemann D p v w z q
  ricci_eq : ∀ (D : LeafwiseLeviCivitaFamily R.spacetime R.slices)
    (D' : LeafwiseLeviCivitaFamily P.realization.spacetime P.realization.slices)
    (p : R.spacetime.Point) (v w : R.spacetime.Horizontal p),
    horizontalRicci D' p (P.horizontal p v) (P.horizontal p w) = horizontalRicci D p v w
  scalar_eq : ∀ (D : LeafwiseLeviCivitaFamily R.spacetime R.slices)
    (D' : LeafwiseLeviCivitaFamily P.realization.spacetime P.realization.slices)
    (p : R.spacetime.Point), horizontalScalarCurvature D' p = horizontalScalarCurvature D p / Q
  norm_eq : ∀ (D : LeafwiseLeviCivitaFamily R.spacetime R.slices)
    (D' : LeafwiseLeviCivitaFamily P.realization.spacetime P.realization.slices)
    (p : R.spacetime.Point), horizontalCurvatureNorm D' p = horizontalCurvatureNorm D p / Q
  normSq_eq : ∀ (D : LeafwiseLeviCivitaFamily R.spacetime R.slices)
    (D' : LeafwiseLeviCivitaFamily P.realization.spacetime P.realization.slices)
    (p : R.spacetime.Point), horizontalCurvatureNormSq D' p = horizontalCurvatureNormSq D p / Q ^ 2
  equation_iff : ∀ (D : LeafwiseLeviCivitaFamily R.spacetime R.slices)
    (D' : LeafwiseLeviCivitaFamily P.realization.spacetime P.realization.slices),
    IntrinsicGeneralizedRicciEquation D' ↔ IntrinsicGeneralizedRicciEquation D
  time_bracket : ∀ (U : Set R.spacetime.Point), IsOpen U →
    ∀ V : HorizontalSection R.spacetime, IsSmoothHorizontalSectionOn R.spacetime V U →
      ∀ p ∈ U, horizontalTimeBracket P.realization.spacetime (parabolicHorizontalSection P V) p =
        (1 / Q : ℝ) • P.horizontal p (horizontalTimeBracket R.spacetime V p)
  leafwise_connection : ∀ (D : LeafwiseLeviCivitaFamily R.spacetime R.slices)
    (D' : LeafwiseLeviCivitaFamily P.realization.spacetime P.realization.slices)
    (U : Set R.spacetime.Point), IsOpen U →
    ∀ V : HorizontalSection R.spacetime, IsSmoothHorizontalSectionOn R.spacetime V U →
      ∀ p ∈ U, ∀ v : R.spacetime.Horizontal p,
        rawLeafwiseCovariantDerivative D' (parabolicHorizontalSection P V) p (P.horizontal p v) =
          P.horizontal p (rawLeafwiseCovariantDerivative D V p v)
  horizontal_connection : ∀ (D : LeafwiseLeviCivitaFamily R.spacetime R.slices)
    (D' : LeafwiseLeviCivitaFamily P.realization.spacetime P.realization.slices)
    (U : Set R.spacetime.Point), IsOpen U →
    ∀ V : HorizontalSection R.spacetime, IsSmoothHorizontalSectionOn R.spacetime V U →
      ∀ p ∈ U, ∀ Z : TangentSpace (spacetimeModel n) p,
        rawHorizontalCovariantDerivative D' (parabolicHorizontalSection P V) p Z =
          P.horizontal p (rawHorizontalCovariantDerivative D V p Z)
  backward_time : ∀ (γ : ℝ → R.spacetime.Point) (J : Set ℝ) (T : ℝ),
    (∀ τ ∈ J, R.spacetime.timeFunction (γ τ) = T - τ) →
    ∀ s : ℝ, s / Q ∈ J →
      P.realization.spacetime.timeFunction (parabolicBackwardCurve Q γ s) = parabolicTime Q a T - s
  backward_derivative : ∀ (γ : ℝ → R.spacetime.Point) (s : ℝ),
    MDifferentiableAt 𝓘(ℝ) (spacetimeModel n) γ (s / Q) →
    (show SpacetimeModelVector n from
      mfderiv 𝓘(ℝ) (spacetimeModel n)
        (show ℝ → P.realization.spacetime.Point from parabolicBackwardCurve Q γ) s
        (show TangentSpace 𝓘(ℝ) s from (1 : ℝ))) =
      (1 / Q : ℝ) • (mfderiv 𝓘(ℝ) (spacetimeModel n) γ (s / Q)
        (show TangentSpace 𝓘(ℝ) (s / Q) from (1 : ℝ)))
  backward_velocity_val : ∀ (γ : ℝ → R.spacetime.Point) (τ : ℝ),
    MDifferentiableAt 𝓘(ℝ) (spacetimeModel n) γ τ →
    HasDerivAt (fun s ↦ R.spacetime.timeFunction (γ s)) (-1) τ →
    (backwardHorizontalVelocity R.spacetime γ τ).val =
      mfderiv 𝓘(ℝ) (spacetimeModel n) γ τ (show TangentSpace 𝓘(ℝ) τ from (1 : ℝ)) +
        R.spacetime.timeVector (γ τ)
  backward_velocity : ∀ (γ : ℝ → R.spacetime.Point) (s : ℝ),
    MDifferentiableAt 𝓘(ℝ) (spacetimeModel n) γ (s / Q) →
    backwardHorizontalVelocity P.realization.spacetime (parabolicBackwardCurve Q γ) s =
      (1 / Q : ℝ) • P.horizontal (γ (s / Q)) (backwardHorizontalVelocity R.spacetime γ (s / Q))
  backward_energy : ∀ (γ : ℝ → R.spacetime.Point) (s : ℝ),
    MDifferentiableAt 𝓘(ℝ) (spacetimeModel n) γ (s / Q) →
    P.realization.spacetime.horizontalMetric.inner (γ (s / Q))
      (backwardHorizontalVelocity P.realization.spacetime (parabolicBackwardCurve Q γ) s)
      (backwardHorizontalVelocity P.realization.spacetime (parabolicBackwardCurve Q γ) s) =
      R.spacetime.horizontalMetric.inner (γ (s / Q))
        (backwardHorizontalVelocity R.spacetime γ (s / Q))
        (backwardHorizontalVelocity R.spacetime γ (s / Q)) / Q

end PoincareConjecture
