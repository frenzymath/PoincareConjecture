import PoincareConjecture.Statements.Ch04.CurvatureTheory
import PoincareConjecture.Proofs.M04.CurvatureCalculus
import PoincareConjecture.Proofs.M04.TensorNorm
import PoincareConjecture.Proofs.M04.ScalarEvolution
import PoincareConjecture.Proofs.M04.TensorEvolution
import PoincareConjecture.Proofs.M04.DerivativeEstimates
import PoincareConjecture.Proofs.M04.MetricComparison
import PoincareConjecture.Proofs.M04.CurvaturePositivity
import PoincareConjecture.Proofs.Ch04.ScalarBounds










set_option autoImplicit false

universe u

namespace PoincareConjecture


















theorem ricciFlowCurvatureTheory : RicciFlowCurvatureTheory.{u} := by
  exact {
    tensor_calculus := @LeviCivitaData.curvatureTensorCalculus
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

end PoincareConjecture
