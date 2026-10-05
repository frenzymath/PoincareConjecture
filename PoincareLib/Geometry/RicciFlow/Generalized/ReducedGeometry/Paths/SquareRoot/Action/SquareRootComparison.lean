import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Coordinates.GaugeVelocity
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Paths.SquareRoot.Action.SquareRootVelocityExtension

/-!
# Comparing square-root velocities on a common parameter subset

Morgan-Tian Lemma 6.8 and Lemma 6.18, pp. 108-109, 113-114.
The prescribed horizontal velocity equals the projection of the
actual derivative restricted to any uniquely differentiable subset.
Equality of paths on that subset therefore identifies their velocities.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

/-- Restriction of the actual within derivative preserves the
supplied square-root horizontal velocity, including closed endpoints,
Lemma 6.8, pp. 108-109. -/
theorem squareRoot_projectedVelocityWithin_subset
    {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
    (R : M14SquareRootPath G p) {J : Set ℝ}
    (hsub : J ⊆ M14SqrtParameterInterval τ₁ τ₂) {s : ℝ} (hs : s ∈ J)
    (hJ : UniqueDiffWithinAt ℝ J s) :
    projectedCurveVelocityWithin G R.curve J s = R.horizontal_velocity s := by
  unfold projectedCurveVelocityWithin
  rw [mfderivWithin_subset hsub hJ.uniqueMDiffWithinAt
    ((R.smooth.mono R.interval_subset s (hsub hs)).mdifferentiableWithinAt (by simp))]
  exact (squareRoot_horizontalVelocity_eq_projection R (hsub hs)).symm

/-- Square-root paths equal on a uniquely differentiable common
subset have the same actual horizontal velocities there, the
derivative comparison used in Lemma 6.18, pp. 113-114. -/
theorem squareRoot_horizontalVelocity_heq_on_subset
    {T₁ T₂ τ₁ τ₂ σ₁ σ₂ : ℝ} {x₁ y₁ x₂ y₂ : G.Point}
    {p₁ : M14BackwardPath G T₁ τ₁ τ₂ x₁ y₁} {p₂ : M14BackwardPath G T₂ σ₁ σ₂ x₂ y₂}
    (R₁ : M14SquareRootPath G p₁) (R₂ : M14SquareRootPath G p₂) {J : Set ℝ}
    (hsub₁ : J ⊆ M14SqrtParameterInterval τ₁ τ₂)
    (hsub₂ : J ⊆ M14SqrtParameterInterval σ₁ σ₂)
    (heq : EqOn R₁.curve R₂.curve J) {s : ℝ} (hs : s ∈ J)
    (hJ : UniqueDiffWithinAt ℝ J s) :
    HEq (R₁.horizontal_velocity s) (R₂.horizontal_velocity s) := by
  rw [← squareRoot_projectedVelocityWithin_subset R₁ hsub₁ hs hJ,
    ← squareRoot_projectedVelocityWithin_subset R₂ hsub₂ hs hJ]
  exact projectedCurveVelocityWithin_congrOn heq hs

end PoincareMT.M14
