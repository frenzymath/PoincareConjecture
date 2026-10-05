import PoincareLib.Geometry.Spacetime.Rescaling.Basic
import PoincareLib.Geometry.Spacetime.Horizontal.Basic

/-! Ported from Mapher06/Poincare-MorganTian, `PoincareMT/Definitions/M13HorizontalTransport.lean`,
revision `49331b7d7ecad38f53e4300c3b35d6a84b2cc648`.
Declaration bodies are unchanged; only imports and module placement differ. -/

/-!
# Raw horizontal transport and backward curves

Morgan-Tian Definition 3.40, p. 61, and Lemma 6.72, pp. 141-142. These
definitions use the actual spacetime derivative and literal horizontal
projection. A backward clock identity is needed to identify the projected
velocity with gamma' + chi; it is not assumed by the raw operation itself.
No L-action, exponential, or existence assertion is defined here.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {A : AdaptedMetricAtlas n X} {R : GeneralizedFlowCarrierConclusion A}
  {Q : ℝ} {hQ : 0 < Q} {a : ℝ}

/-- A section transported by the actual identity on underlying horizontal vectors. -/
noncomputable def parabolicHorizontalSection (P : ParabolicSpacetimeRescaling R Q hQ a)
    (V : HorizontalSection R.spacetime) : HorizontalSection P.realization.spacetime :=
  fun p ↦ P.horizontal p (V p)

/-- The inverse-scale reparameterization of the actual point curve. -/
noncomputable def parabolicBackwardCurve (Q : ℝ) (γ : ℝ → X) : ℝ → X := fun s ↦ γ (s / Q)

/-- Exact image of a backward-time domain under tau' = Q*tau. -/
def parabolicBackwardDomain (Q : ℝ) (J : Set ℝ) : Set ℝ := (fun τ ↦ Q * τ) '' J

/-- The actual horizontal component of the velocity of a spacetime curve. -/
noncomputable def backwardHorizontalVelocity {time : X → ℝ} {I : SpacetimeInterval}
    (F : GeneralizedFlowSpacetime n X time I) (γ : ℝ → F.Point) (τ : ℝ) :
    F.Horizontal (γ τ) :=
  F.horizontalProjection (γ τ)
    (mfderiv 𝓘(ℝ) (spacetimeModel n) γ τ
      (show TangentSpace 𝓘(ℝ) τ from (1 : ℝ)))

/-- The within-domain horizontal velocity, retaining included time endpoints. -/
noncomputable def backwardHorizontalVelocityWithin {time : X → ℝ} {I : SpacetimeInterval}
    (F : GeneralizedFlowSpacetime n X time I) (γ : ℝ → F.Point) (J : Set ℝ) (τ : ℝ) :
    F.Horizontal (γ τ) :=
  F.horizontalProjection (γ τ)
    (mfderivWithin 𝓘(ℝ) (spacetimeModel n) γ J τ
      (show TangentSpace 𝓘(ℝ) τ from (1 : ℝ)))

/-- An invertible linear comparison preserving the two selected inner products.
The prescribed map is kappa/sqrt(Q), hence a linear isometry for those metrics.
Its existence is an M13 output. -/
structure ParabolicNormalizedHorizontalIsometry
    (P : ParabolicSpacetimeRescaling R Q hQ a) where
  linearEquiv : ∀ p : R.spacetime.Point,
    R.spacetime.Horizontal p ≃L[ℝ] P.realization.spacetime.Horizontal p
  linearEquiv_eq : ∀ (p : R.spacetime.Point) (v : R.spacetime.Horizontal p),
    linearEquiv p v = (1 / Real.sqrt Q : ℝ) • P.horizontal p v
  inner_eq : ∀ (p : R.spacetime.Point) (v w : R.spacetime.Horizontal p),
    P.realization.spacetime.horizontalMetric.inner p (linearEquiv p v) (linearEquiv p w) =
      R.spacetime.horizontalMetric.inner p v w

end PoincareMT
