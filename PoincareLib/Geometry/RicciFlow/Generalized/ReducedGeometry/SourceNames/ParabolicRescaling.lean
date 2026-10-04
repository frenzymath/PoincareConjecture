import PoincareLib.Geometry.RicciFlow.Rescaling.Generalized
import PoincareLib.Geometry.Spacetime.Rescaling.Geometry.Carrier
import PoincareLib.Geometry.Spacetime.Rescaling.Horizontal.SliceConnection
import PoincareLib.Geometry.Spacetime.Rescaling.Interval.Smooth

/-! Source-name facade for the unchanged Mapher proof bodies. -/

namespace PoincareMT.M13

export PoincareMT.ParabolicRescaling
  (intervalChartExtension_contDiffOn
   intervalChartExtension_val
   parabolicClock_derivative
   parabolicIntervalTransport
   parabolicLeafwiseConnection
   parabolicSliceIdentification
   parabolicSliceIdentification_metric
   parabolicSliceIdentification_tangent
   parabolicSliceIdentification_val
   parabolicSpacetime
   parabolicSpacetimeHorizontal
   parabolicSpacetimeHorizontal_smooth
   parabolicSpacetimeHorizontal_val
   parabolicSpacetimeIdentification
   parabolicSpacetimeIdentification_derivative
   parabolicSpacetimeIdentification_eq
   parabolicSpacetimeSlice
   parabolicSpacetime_metric
   parabolicSpacetime_projection
   parabolic_leafwise_chosen
   scaled_reparameterized_smooth)

export PoincareMT.Homothety (scaleSmoothMetric scaleSmoothMetric_inner)

end PoincareMT.M13
