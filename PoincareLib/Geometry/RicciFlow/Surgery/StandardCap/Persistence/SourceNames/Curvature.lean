import PoincareLib.Geometry.RicciFlow.Curvature.Estimates.QuadraticRicci
import PoincareLib.Geometry.RicciFlow.Positivity.Sectional.MinimumDiffusion
import PoincareLib.Geometry.Riemannian.Coordinates.Exponential.JetBounds.TensorPullback

/-! Compatibility names for the unchanged Mapher cap-persistence proof. -/

namespace PoincareMT.M04

export PoincareMT.RicciFlowAnalysis
  (abs_ricci_le_curvatureTensorNorm
   covariantTensorDerivative_metricGramEvaluation
   curvatureTensor_cyclic
   curvatureTensor_pair_exchange
   curvatureTensor_swap_first
   metricGramEvaluation)

end PoincareMT.M04
