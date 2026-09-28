import PoincareConjecture.Proofs.M14.Sec6_5_PositiveStartFormula
import PoincareConjecture.Proofs.M14.Sec6_5_PositiveStartLaplacian
import PoincareConjecture.Proofs.M14.Sec6_2_MinimizerEuler

set_option autoImplicit false

open Set
open scoped Manifold ContDiff intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval}

theorem positiveStartCorrectionStatement
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (G : GeneralizedLGeometryTransport n X time I) :
    M14PositiveStartCorrectionStatement G := by
  intro T a b x y p ha hp U hU hy _ hf hstart hderiv
  obtain ⟨E, hEuler⟩ := minimizerEulerStatement hCoordinates hM12 T a b x y p hp
  let R := squareRootPathOfEuler p hCoordinates hM12 E hEuler
  let dR := fun t => M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise)
    (p.curve t)
  let K := M14GeneralizedKIntegral G p dR
  let C := Real.rpow (a / b) (3 / 2 : ℝ) *
    (horizontalScalarCurvature G.leafwise (p.curve a) +
      G.spacetime.horizontalMetric.inner (p.curve a)
        (p.horizontal_velocity a) (p.horizontal_velocity a))
  let Kshift := ∫ t in a..b, Real.sqrt t * (Real.sqrt t - Real.sqrt a) ^ 2 *
    M14GeneralizedHarnackDensity G p dR t
  obtain ⟨B, hB⟩ := exists_orthonormal_horizontalBasis G y
  have hform := positiveStart_time_gradient_identities hCoordinates hM12 ha hp R
    U hU hy hf hstart hderiv B hB
  refine ⟨C, K, Kshift, rfl, rfl, rfl, E, hEuler, B, hB, hform.1, hform.2, ?_⟩
  have hs : Real.sqrt b ∈ M14SqrtParameterInterval a b :=
    ⟨Real.sqrt_le_sqrt p.tau_lt.le, le_rfl⟩
  have hpoint : R.curve (Real.sqrt b) = y := by
    rw [R.agrees _ hs, Real.sq_sqrt (ha.trans p.tau_lt).le, p.curve_end]
  have hq : G.spacetime.timeFunction (R.curve (Real.sqrt b)) = T - b := by
    rw [R.curve_time _ hs, Real.sq_sqrt (ha.trans p.tau_lt).le]
  refine ⟨⟨R.curve (Real.sqrt b), hq⟩, hpoint, ?_⟩
  have h := positiveStart_laplacian_bound hCoordinates hM04 hM12 hp R U hU hy hf hq
  rwa [congrArg (horizontalScalarCurvature G.leafwise) hpoint] at h

end PoincareConjecture.M14
