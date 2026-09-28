import PoincareConjecture.Definitions.M14Exponential










set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

private theorem transport_horizontal_tangent {x y : G.Point} (h : x = y)
    (v : G.Horizontal x) :
    (h ▸ v.val : TangentSpace (spacetimeModel n) y) = (h ▸ v : G.Horizontal y).val := by
  cases h
  rfl




theorem initialValuePath_initial_derivative {T τ : ℝ} {x y : G.Point} {Z : G.Horizontal x}
    (P : M14SquareRootInitialValuePath G T τ x y Z) :
    ∃ h : P.square_path.curve 0 = x,
      h ▸ mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) P.square_path.curve
        (M14SqrtParameterInterval 0 τ) 0 (1 : ℝ) =
          (2 : ℝ) • (Z : TangentSpace (spacetimeModel n) x) := by
  obtain ⟨h, hv⟩ := P.initial_velocity
  refine ⟨h, ?_⟩
  have hzero : (0 : ℝ) ∈ M14SqrtParameterInterval 0 τ :=
    ⟨by rw [Real.sqrt_zero], Real.sqrt_nonneg τ⟩
  have hd := P.square_path.derivative_eq 0 hzero
  simp only [mul_zero, neg_zero, zero_smul, zero_add] at hd
  rw [hd, transport_horizontal_tangent h, hv]
  rfl

end PoincareConjecture.M14
