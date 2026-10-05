import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Construction.MetricCombination
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Construction.MetricPullback
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Curvature.Conformal.ConformalSectional
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Cylinder.CylinderChartMetric
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Cylinder.CylinderGram
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Neck.NeckMetricBound

/-! Source-name facade for the preserved Mapher area and width proofs. -/

namespace PoincareMT.M36
export PoincareMT.MetricSurgery (
  contMDiff_exp_neg_two
  metricPullbackForm
  metricPullbackForm_apply
  metricPullbackForm_contMDiffAt
  metricPullbackForm_coordinates
  positiveScaling
  positiveScaling_inner
  sectionalCurvature_positiveScaling_exp
  sphere_chart_center_zero
  sphere_chart_differential_inner_at
  sphere_chart_inverse_fderiv_inner
  sphere_inclusion_inner)
end PoincareMT.M36
