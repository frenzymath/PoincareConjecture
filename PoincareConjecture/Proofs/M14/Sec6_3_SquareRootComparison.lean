import PoincareConjecture.Proofs.M14.Sec6_4_GaugeVelocity
import PoincareConjecture.Proofs.M14.Sec6_2_SquareRootVelocityExtension










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}




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

end PoincareConjecture.M14
