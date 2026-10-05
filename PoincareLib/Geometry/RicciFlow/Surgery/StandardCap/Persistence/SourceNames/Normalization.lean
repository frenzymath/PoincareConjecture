import PoincareLib.Geometry.Riemannian.Normalization.Metric.Construction
import PoincareLib.Geometry.Riemannian.Normalization.Scaling.Curvature
import PoincareLib.Geometry.Riemannian.Normalization.Scaling.Distance
import PoincareLib.Geometry.Riemannian.Normalization.Scaling.Volume

/-! Compatibility names for the unchanged Mapher cap-persistence proof. -/

namespace PoincareMT

alias m01RescaledMetric := rescaledMetric
alias m01RescaledMetric_ball := rescaledMetric_ball
alias m01RescaledMetric_connection := rescaledMetric_connection
alias m01RescaledMetric_curvatureTensor := rescaledMetric_curvatureTensor
alias m01RescaledMetric_edist := rescaledMetric_edist
alias m01RescaledMetric_inner := rescaledMetric_inner
alias m01RescaledMetric_pathELength := rescaledMetric_pathELength

attribute [reducible] m01RescaledMetric m01RescaledMetric_connection

end PoincareMT
