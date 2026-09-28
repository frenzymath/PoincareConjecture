import PoincareConjecture.Proofs.M14.Sec6_2_MovingMetric
import PoincareConjecture.Proofs.M14.Sec6_2_SquareRootVelocityExtension
import PoincareConjecture.Statements.M12GeneralizedEquation

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}

theorem squareRoot_scalar_contDiffOn
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (R : M14SquareRootPath G p) :
    ContDiffOn ℝ ∞ (fun s => horizontalScalarCurvature G.leafwise (R.curve s))
      (M14SqrtParameterInterval τ₁ τ₂) := by
  have H := (hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise
  exact (H.scalar_smooth.comp_contMDiffOn (R.smooth.mono R.interval_subset)).contDiffOn

theorem squareRoot_energy_contDiffOn (R : M14SquareRootPath G p) :
    ContDiffOn ℝ ∞ (fun s => G.spacetime.horizontalMetric.inner (R.curve s)
      (R.horizontal_velocity s) (R.horizontal_velocity s))
      (M14SqrtParameterInterval τ₁ τ₂) := by
  have hR := R.smooth.mono R.interval_subset
  have hA := squareRoot_horizontalVelocity_smooth R
  have hpair := (G.spacetime.horizontalMetric.contMDiff.comp_contMDiffOn hR).clm_bundle_apply₂
    (F₃ := ℝ) (E₃ := Bundle.Trivial G.Point ℝ) hA hA
  apply ContMDiffOn.contDiffOn
  intro s hs
  simpa only [Bundle.Trivial.fiberBundle_trivializationAt', Bundle.Trivial.trivialization_apply]
    using (Bundle.contMDiffWithinAt_totalSpace.mp (hpair s hs)).2

set_option backward.isDefEq.respectTransparency false in

theorem squareRoot_scalar_hasDerivWithinAt
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (R : M14SquareRootPath G p)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂) :
    HasDerivWithinAt (fun r => horizontalScalarCurvature G.leafwise (R.curve r))
      (2 * s * M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise) (R.curve s) +
        M14HorizontalScalarDifferential G (R.curve s) (R.horizontal_velocity s).val)
      (M14SqrtParameterInterval τ₁ τ₂) s := by
  have H := (hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise
  have hR := ((R.smooth.mono R.interval_subset) s hs).mdifferentiableWithinAt (by simp)
  have hd := (H.scalar_smooth.mdifferentiable (by simp) (R.curve s)).hasMFDerivAt
  have hcomp := hd.comp_hasMFDerivWithinAt s hR.hasMFDerivWithinAt
  have hscalar := hcomp.hasFDerivWithinAt.hasDerivWithinAt
  change HasDerivWithinAt (fun r => horizontalScalarCurvature G.leafwise (R.curve r))
    (M14HorizontalScalarDifferential G (R.curve s)
      (mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) R.curve
        (M14SqrtParameterInterval τ₁ τ₂) s (1 : ℝ))) _ s at hscalar
  rw [R.derivative_eq s hs, map_add, map_smul, smul_eq_mul] at hscalar
  convert hscalar using 1
  unfold M14BackwardTimeDerivative M14HorizontalScalarDifferential
  ring

theorem squareRoot_energy_hasDerivWithinAt (R : M14SquareRootPath G p)
    (E : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂)
      R.horizontal_velocity) {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂)
    (hEuler : ∀ W, M14SquareRootEulerResidual G R E s W = 0) :
    HasDerivWithinAt (fun r => G.spacetime.horizontalMetric.inner (R.curve r)
      (R.horizontal_velocity r) (R.horizontal_velocity r))
      (4 * s ^ 2 * M14HorizontalScalarDifferential G (R.curve s)
          (R.horizontal_velocity s).val -
        4 * s * horizontalRicci G.leafwise (R.curve s)
          (R.horizontal_velocity s) (R.horizontal_velocity s))
      (M14SqrtParameterInterval τ₁ τ₂) s := by
  have h := squareRoot_covariantDerivative_metric_product R E E hs
  have hE := hEuler (R.horizontal_velocity s)
  unfold M14SquareRootEulerResidual M14SquareRootVelocity at hE
  rw [G.spacetime.horizontalMetric.symm (R.curve s) (R.horizontal_velocity s)] at h
  convert h using 1
  linarith

end PoincareConjecture.M14
