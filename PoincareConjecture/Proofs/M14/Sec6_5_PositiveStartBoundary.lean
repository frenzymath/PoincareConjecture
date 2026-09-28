import PoincareConjecture.Proofs.M14.Sec6_5_PositiveStartInitialVelocity
import PoincareConjecture.Proofs.M14.Sec6_5_HarnackIntegral
import PoincareConjecture.Proofs.M14.Sec6_2_SquareEuler

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}

theorem positiveStart_initial_harnackPrimitive (R : M14SquareRootPath G p)
    (hstart : MDifferentiableWithinAt (𝓘(ℝ, ℝ)) (spacetimeModel n)
      p.curve (Icc a b) a)
    (hderiv : mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) p.curve (Icc a b) a 1 =
      -G.spacetime.timeVector (p.curve a) + (p.horizontal_velocity a).val) :
    squareHarnackPrimitive R (Real.sqrt a) = a * Real.sqrt a *
      (horizontalScalarCurvature G.leafwise (p.curve a) +
        G.spacetime.horizontalMetric.inner (p.curve a)
          (p.horizontal_velocity a) (p.horizontal_velocity a)) := by
  have hpoint : R.curve (Real.sqrt a) = p.curve a := by
    rw [R.agrees _ ⟨le_rfl, Real.sqrt_le_sqrt p.tau_lt.le⟩,
      Real.sq_sqrt p.tau_nonneg]
  unfold squareHarnackPrimitive
  rw [positiveStart_initial_velocity_norm R hstart hderiv,
    congrArg (horizontalScalarCurvature G.leafwise) hpoint,
    show (Real.sqrt a) ^ 3 = a * Real.sqrt a by
      rw [pow_succ, Real.sq_sqrt p.tau_nonneg]]
  ring

theorem positiveStart_harnackIntegral_eq
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (hp : M14IsMinimizing p)
    (R : M14SquareRootPath G p)
    (hstart : MDifferentiableWithinAt (𝓘(ℝ, ℝ)) (spacetimeModel n)
      p.curve (Icc a b) a)
    (hderiv : mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) p.curve (Icc a b) a 1 =
      -G.spacetime.timeVector (p.curve a) + (p.horizontal_velocity a).val) :
    M14GeneralizedKIntegral G p
        (fun t => M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise)
          (p.curve t)) =
      M14BackwardLAction G p / 2 -
        ((Real.sqrt b) ^ 3 * horizontalScalarCurvature G.leafwise (R.curve (Real.sqrt b)) +
          Real.sqrt b * G.spacetime.horizontalMetric.inner (R.curve (Real.sqrt b))
            (R.horizontal_velocity (Real.sqrt b)) (R.horizontal_velocity (Real.sqrt b)) / 4) +
        a * Real.sqrt a * (horizontalScalarCurvature G.leafwise (p.curve a) +
          G.spacetime.horizontalMetric.inner (p.curve a)
            (p.horizontal_velocity a) (p.horizontal_velocity a)) := by
  obtain ⟨E⟩ := exists_squareRoot_velocity_extension R
  have h := squareRoot_harnackIntegral_eq hM12 R E (by
    intro r hr W
    exact squareRootEulerResidual_eq_zero_of_minimizing hCoordinates hM12 hp E
      (Ioo_subset_Icc_self hr) W)
  rw [positiveStart_initial_harnackPrimitive R hstart hderiv] at h
  exact h

end PoincareConjecture.M14
