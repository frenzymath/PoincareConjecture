import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Comparison.SourceGaussian
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Exponential.InitialTime.InitialJacobianCalculus
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Exponential.Jacobian.JacobianEvolution
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Exponential.Jacobian.WeightedJacobian
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Measure.Chart.ChartIntegralTransport
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Measure.Transport.CalibratedTransport
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Measure.Transport.PullbackJacobian
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Regularity.AlmostEverywhere.RegularImage
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Regularity.Continuity.MinimizingLifts

/-! Source-name facade for the unchanged Mapher proof bodies. -/

namespace PoincareMT.M10

export PoincareMT.ReducedVolume
  (backwardLLength_eq_of_eqOn
   calibratedMetricVolume_image_eq_lintegral
   hasDerivAt_jacobian_of_scaled_normalized_gram
   integrableOn_calibrated_iff_pullback
   integralOn_calibrated_eq_pullback
   integral_sourceGaussian
   map_inverse_restrict_apply
   measure_eq_of_local_comparisons
   minimizing_of_eqOn
   pullbackJacobian
   pullbackJacobian_continuousAt
   pullbackJacobian_nonneg
   regularImage_slice_complement_eq_zero
   sourceGaussian_integrable
   tendsto_scaled_sqrt_det
   weightedJacobian_hasDerivAt)

end PoincareMT.M10
