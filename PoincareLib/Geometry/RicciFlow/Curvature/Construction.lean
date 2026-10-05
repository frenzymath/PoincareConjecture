import PoincareLib.Geometry.RicciFlow.Curvature.Theory
import PoincareLib.Geometry.Riemannian.Curvature.IntrinsicCalculus
import PoincareLib.Geometry.Riemannian.Coordinates.Exponential.JetBounds.TensorPullback
import PoincareLib.Geometry.RicciFlow.Curvature.Evolution.Scalar.Within
import PoincareLib.Geometry.RicciFlow.Curvature.Evolution.Tensor.Within
import PoincareLib.Geometry.RicciFlow.Curvature.Estimates.Derivative
import PoincareLib.Geometry.RicciFlow.MetricComparison.Curvature
import PoincareLib.Geometry.RicciFlow.Positivity.Preservation
import PoincareLib.Geometry.RicciFlow.Curvature.Bounds.Scalar

/-! Adapted from Mapher06/Poincare-MorganTian, `PoincareMT/Proofs/M04.lean`,
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. See the curvature import record under
`references/ricci-flow/mapher/curvature/`. -/

/-!
# Curvature theory of Ricci flow

The fourteen-field theory is assembled from its intrinsic calculus,
within-interval evolution, local estimates, and maximum-principle producers.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- The selected smooth metric and compatible connection satisfy curvature
tensor calculus, and ordinary Ricci flows satisfy scalar, Ricci and Riemann
evolution. Under the stated spacetime curvature and compact-ball controls they
obey Shi derivative estimates and metric comparison. Compact three-dimensional
flows preserve nonnegative sectional/Ricci curvature; connected flows with
nonnegative sectional curvature satisfy scalar-zero rigidity. Given the stated
initial scalar lower bounds, compact flows obey the negative scalar barrier,
including -6 / (1 + 4*t) in dimension three for initial time a >= 0.

Sources: Morgan-Tian Chapter 1, pp. 3-8; Theorem 3.13 and Lemma 3.15,
pp. 41-42; Theorems 3.28-3.29, pp. 51-52; Proposition 4.1, pp. 64-65;
Corollaries 4.14-4.15, pp. 69-70; Theorem 4.18, pp. 71-72.
Use the corrected Ricci contraction and eigenvalue-concavity convention in
`reviews/errata/2026-09-11-tensor-evolution.md`, the scalar sign correction in
`reviews/errata/2026-09-10-analytic-outline-audit.md`, and the retained spacetime
cutoff hypotheses of `reviews/declarations/curvature-estimates-v1.md`.
This established component assembly adds no admission of its own. -/
theorem ricciFlowCurvatureTheory : RicciFlowCurvatureTheory.{u} := by
  exact {
    tensor_calculus := @LeviCivitaData.intrinsicCurvatureTensorCalculus
    curvature_norm_zero := @LeviCivitaData.curvatureDerivativeNorm_zero
    scalar_regular := @RicciFlow.contMDiffOn_scalarCurvature
    scalar_evolution := @RicciFlow.hasDerivWithinAt_scalarCurvature
    curvature_evolution := @RicciFlow.hasDerivWithinAt_curvatureTensor
    ricci_evolution := @RicciFlow.hasDerivWithinAt_ricci
    local_derivative_estimates := @local_curvatureDerivative_bound
    initial_derivative_estimates := @local_curvatureDerivative_bound_of_initial
    metric_comparison := @RicciFlow.metric_comparison_of_curvature_bound
    sectional_preservation := @RicciFlow.nonnegativeSectionalCurvature_preserved
    ricci_preservation := @RicciFlow.nonnegativeRicciCurvature_preserved
    scalar_zero_rigidity := @RicciFlow.flat_of_scalarCurvature_eq_zero
    scalar_lower_bound := @RicciFlow.scalarCurvature_lowerBound
    normalized_scalar_lower_bound := @RicciFlow.scalarCurvature_lowerBound_three }

end PoincareMT
