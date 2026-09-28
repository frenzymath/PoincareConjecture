import PoincareConjecture.Definitions.M13SpacetimeRescaling
import PoincareConjecture.Definitions.M12HorizontalCalculus











set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {A : AdaptedMetricAtlas n X} {R : GeneralizedFlowCarrierConclusion A}
  {Q : ℝ} {hQ : 0 < Q} {a : ℝ}


noncomputable def parabolicHorizontalSection (P : ParabolicSpacetimeRescaling R Q hQ a)
    (V : HorizontalSection R.spacetime) : HorizontalSection P.realization.spacetime :=
  fun p ↦ P.horizontal p (V p)


noncomputable def parabolicBackwardCurve (Q : ℝ) (γ : ℝ → X) : ℝ → X := fun s ↦ γ (s / Q)


def parabolicBackwardDomain (Q : ℝ) (J : Set ℝ) : Set ℝ := (fun τ ↦ Q * τ) '' J


noncomputable def backwardHorizontalVelocity {time : X → ℝ} {I : SpacetimeInterval}
    (F : GeneralizedFlowSpacetime n X time I) (γ : ℝ → F.Point) (τ : ℝ) :
    F.Horizontal (γ τ) :=
  F.horizontalProjection (γ τ)
    (mfderiv 𝓘(ℝ) (spacetimeModel n) γ τ
      (show TangentSpace 𝓘(ℝ) τ from (1 : ℝ)))


noncomputable def backwardHorizontalVelocityWithin {time : X → ℝ} {I : SpacetimeInterval}
    (F : GeneralizedFlowSpacetime n X time I) (γ : ℝ → F.Point) (J : Set ℝ) (τ : ℝ) :
    F.Horizontal (γ τ) :=
  F.horizontalProjection (γ τ)
    (mfderivWithin 𝓘(ℝ) (spacetimeModel n) γ J τ
      (show TangentSpace 𝓘(ℝ) τ from (1 : ℝ)))




structure ParabolicNormalizedHorizontalIsometry
    (P : ParabolicSpacetimeRescaling R Q hQ a) where
  linearEquiv : ∀ p : R.spacetime.Point,
    R.spacetime.Horizontal p ≃L[ℝ] P.realization.spacetime.Horizontal p
  linearEquiv_eq : ∀ (p : R.spacetime.Point) (v : R.spacetime.Horizontal p),
    linearEquiv p v = (1 / Real.sqrt Q : ℝ) • P.horizontal p v
  inner_eq : ∀ (p : R.spacetime.Point) (v w : R.spacetime.Horizontal p),
    P.realization.spacetime.horizontalMetric.inner p (linearEquiv p v) (linearEquiv p w) =
      R.spacetime.horizontalMetric.inner p v w

end PoincareConjecture
