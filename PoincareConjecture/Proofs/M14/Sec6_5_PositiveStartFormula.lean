import PoincareConjecture.Proofs.M14.Sec6_5_PositiveStartTimeDerivative
import PoincareConjecture.Proofs.M14.Sec6_5_PositiveStartGradient
import PoincareConjecture.Proofs.M14.Sec6_5_PositiveStartBoundary
import PoincareConjecture.Proofs.M14.Sec6_5_PositiveStartAlgebra

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}

theorem positiveStart_time_gradient_identities
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (ha : 0 < a) (hp : M14IsMinimizing p)
    (R : M14SquareRootPath G p)
    (U : Set G.Point) (hU : IsOpen U) (hy : y ∈ U)
    (hf : ContMDiffOn (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞
      (M14ReducedLengthAt G T a x) U)
    (hstart : MDifferentiableWithinAt (𝓘(ℝ, ℝ)) (spacetimeModel n)
      p.curve (Icc a b) a)
    (hderiv : mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) p.curve (Icc a b) a 1 =
      -G.spacetime.timeVector (p.curve a) + (p.horizontal_velocity a).val)
    (B : Module.Basis (Fin n) ℝ (G.Horizontal y))
    (hB : ∀ i j, G.spacetime.horizontalMetric.inner y (B i) (B j) =
      if i = j then 1 else 0) :
    let K := M14GeneralizedKIntegral G p
      (fun t => M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise) (p.curve t))
    let C := Real.rpow (a / b) (3 / 2 : ℝ) *
      (horizontalScalarCurvature G.leafwise (p.curve a) +
        G.spacetime.horizontalMetric.inner (p.curve a)
          (p.horizontal_velocity a) (p.horizontal_velocity a))
    M14BackwardTimeDerivative G (M14ReducedLengthAt G T a x) y =
        horizontalScalarCurvature G.leafwise y - M14ReducedLengthValue G T a b x y / b +
          K / (2 * b * Real.sqrt b) - C / 2 ∧
      M14ReducedLengthGradientNormSq (T := T) (τ₁ := a) G x y B =
        M14ReducedLengthValue G T a b x y / b - K / (b * Real.sqrt b) -
          horizontalScalarCurvature G.leafwise y + C := by
  have hb := ha.trans p.tau_lt
  have hpoint : R.curve (Real.sqrt b) = y := by
    rw [R.agrees _ ⟨Real.sqrt_le_sqrt p.tau_lt.le, le_rfl⟩,
      Real.sq_sqrt hb.le, p.curve_end]
  have hS := congrArg (horizontalScalarCurvature G.leafwise) hpoint
  have ht := positiveStart_time_derivative_square hCoordinates hM12 hp R U hU hy hf
  rw [congrArg (M14BackwardTimeDerivative G (M14ReducedLengthAt G T a x)) hpoint, hS] at ht
  have hK := positiveStart_harnackIntegral_eq hCoordinates hM12 hp R hstart hderiv
  rw [hS] at hK
  have hg := positiveStart_gradient_norm_square hCoordinates hM12 hp R U hU hy hf B hB
  have h := positiveStart_correction_algebra ha hb (M14BackwardLAction G p)
    (G.spacetime.horizontalMetric.inner (R.curve (Real.sqrt b))
      (R.horizontal_velocity (Real.sqrt b)) (R.horizontal_velocity (Real.sqrt b)))
    (horizontalScalarCurvature G.leafwise y)
    (horizontalScalarCurvature G.leafwise (p.curve a) +
      G.spacetime.horizontalMetric.inner (p.curve a)
        (p.horizontal_velocity a) (p.horizontal_velocity a))
    _ _ _ hK ht hg
  rw [← reducedLengthValue_eq_of_minimizing p hp] at h
  exact h

end PoincareConjecture.M14
