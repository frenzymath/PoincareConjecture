import PoincareConjecture.Proofs.M14.Sec6_2_MovingMetric









set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}

set_option backward.isDefEq.respectTransparency false in



theorem squareRoot_scalarField_hasDerivWithinAt (R : M14SquareRootPath G p)
    {f : G.Point → ℝ} {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂)
    (hf : MDifferentiableAt (spacetimeModel n) (𝓘(ℝ, ℝ)) f (R.curve s)) :
    HasDerivWithinAt (fun r => f (R.curve r))
      (2 * s * M14BackwardTimeDerivative G f (R.curve s) +
        mvfderiv (spacetimeModel n) f (R.curve s) (R.horizontal_velocity s).val)
      (M14SqrtParameterInterval τ₁ τ₂) s := by
  have hR := ((R.smooth.mono R.interval_subset) s hs).mdifferentiableWithinAt (by simp)
  have hcomp := hf.hasMFDerivAt.comp_hasMFDerivWithinAt s hR.hasMFDerivWithinAt
  have h := hcomp.hasFDerivWithinAt.hasDerivWithinAt
  change HasDerivWithinAt (fun r => f (R.curve r))
    (mvfderiv (spacetimeModel n) f (R.curve s)
      (mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) R.curve
        (M14SqrtParameterInterval τ₁ τ₂) s (1 : ℝ))) _ s at h
  rw [R.derivative_eq s hs, map_add, map_smul, smul_eq_mul] at h
  convert h using 1
  unfold M14BackwardTimeDerivative
  ring

end PoincareConjecture.M14
