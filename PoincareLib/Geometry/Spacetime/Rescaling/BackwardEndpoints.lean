import PoincareLib.Geometry.Spacetime.Rescaling.Horizontal

/-! Ported from Mapher06/Poincare-MorganTian, `PoincareMT/Statements/M13BackwardEndpoints.lean`,
revision `49331b7d7ecad38f53e4300c3b35d6a84b2cc648`.
Declaration bodies are unchanged; only imports and module placement differ. -/

/-!
# Backward scaling at included endpoints

The affine derivative calculation in Morgan-Tian Lemma 6.72, p. 141,
with the exact time-domain convention of Definition 3.40, p. 61. The
within derivative uses its actual set and a uniqueness-of-derivative
hypothesis; it therefore applies to one-sided interval endpoints without
requiring an extension of the curve or spacetime through that endpoint.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {A : AdaptedMetricAtlas n X} {R : GeneralizedFlowCarrierConclusion A}
  {Q : ℝ} {hQ : 0 < Q} {a : ℝ}

/-- Actual one-sided differential transport on the precise scaled domain. -/
structure ParabolicBackwardEndpointCalculus
    (P : ParabolicSpacetimeRescaling R Q hQ a) : Prop where
  differentiable : ∀ (γ : ℝ → R.spacetime.Point) (J : Set ℝ) (s : ℝ),
    MDifferentiableWithinAt 𝓘(ℝ) (spacetimeModel n) γ J (s / Q) →
    MDifferentiableWithinAt 𝓘(ℝ) (spacetimeModel n)
      (show ℝ → P.realization.spacetime.Point from parabolicBackwardCurve Q γ)
      (parabolicBackwardDomain Q J) s
  derivative : ∀ (γ : ℝ → R.spacetime.Point) (J : Set ℝ) (s : ℝ),
    UniqueDiffWithinAt ℝ J (s / Q) →
    MDifferentiableWithinAt 𝓘(ℝ) (spacetimeModel n) γ J (s / Q) →
    (show SpacetimeModelVector n from
      mfderivWithin 𝓘(ℝ) (spacetimeModel n)
        (show ℝ → P.realization.spacetime.Point from parabolicBackwardCurve Q γ)
        (parabolicBackwardDomain Q J) s (show TangentSpace 𝓘(ℝ) s from (1 : ℝ))) =
      (1 / Q : ℝ) • (mfderivWithin 𝓘(ℝ) (spacetimeModel n) γ J (s / Q)
        (show TangentSpace 𝓘(ℝ) (s / Q) from (1 : ℝ)))
  velocity_val : ∀ (γ : ℝ → R.spacetime.Point) (J : Set ℝ) (τ : ℝ),
    UniqueDiffWithinAt ℝ J τ →
    MDifferentiableWithinAt 𝓘(ℝ) (spacetimeModel n) γ J τ →
    HasDerivWithinAt (fun s ↦ R.spacetime.timeFunction (γ s)) (-1) J τ →
    (backwardHorizontalVelocityWithin R.spacetime γ J τ).val =
      mfderivWithin 𝓘(ℝ) (spacetimeModel n) γ J τ
        (show TangentSpace 𝓘(ℝ) τ from (1 : ℝ)) + R.spacetime.timeVector (γ τ)
  velocity : ∀ (γ : ℝ → R.spacetime.Point) (J : Set ℝ) (s : ℝ),
    UniqueDiffWithinAt ℝ J (s / Q) →
    MDifferentiableWithinAt 𝓘(ℝ) (spacetimeModel n) γ J (s / Q) →
    backwardHorizontalVelocityWithin P.realization.spacetime (parabolicBackwardCurve Q γ)
      (parabolicBackwardDomain Q J) s =
      (1 / Q : ℝ) • P.horizontal (γ (s / Q))
        (backwardHorizontalVelocityWithin R.spacetime γ J (s / Q))
  energy : ∀ (γ : ℝ → R.spacetime.Point) (J : Set ℝ) (s : ℝ),
    UniqueDiffWithinAt ℝ J (s / Q) →
    MDifferentiableWithinAt 𝓘(ℝ) (spacetimeModel n) γ J (s / Q) →
    P.realization.spacetime.horizontalMetric.inner (γ (s / Q))
      (backwardHorizontalVelocityWithin P.realization.spacetime (parabolicBackwardCurve Q γ)
        (parabolicBackwardDomain Q J) s)
      (backwardHorizontalVelocityWithin P.realization.spacetime (parabolicBackwardCurve Q γ)
        (parabolicBackwardDomain Q J) s) =
      R.spacetime.horizontalMetric.inner (γ (s / Q))
        (backwardHorizontalVelocityWithin R.spacetime γ J (s / Q))
        (backwardHorizontalVelocityWithin R.spacetime γ J (s / Q)) / Q

end PoincareMT
