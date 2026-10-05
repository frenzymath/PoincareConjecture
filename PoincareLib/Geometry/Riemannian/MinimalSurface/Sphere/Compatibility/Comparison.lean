import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Distance.LocalSmoothLipschitz
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Smoothing.Charts.CompactMargin
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Smoothing.Charts.Construction
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Smoothing.Charts.Distance
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Smoothing.Charts.Normalization
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Smoothing.Charts.Perturbation
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Smoothing.Euclidean.Approximation
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Smoothing.Euclidean.Blend
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Smoothing.Local.Approximation
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Smoothing.Local.Riemannian
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Smoothing.Local.Supported
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Topology.HomotopyExtension

/-! Source-name facade for the preserved Mapher area and width proofs. -/

namespace PoincareMT.M40
export PoincareMT.SurgeryComparison.Transport (
  chartPerturb
  chartPerturb_eq_of_zero
  chartPerturb_eventuallyEq
  chartPerturb_of_mem
  chartSmoothingDisplacement
  contMDiffAt_chartPerturb_of_mem
  contMDiffAt_supportedChartSmoothing_of_contMDiffAt
  contMDiffAt_supportedChartSmoothing_of_eventuallyEq_one
  continuous_supportedChartSmoothing
  cutoffBlend
  cutoffBlend_dist_le
  eventually_norm_mfderiv_lt
  exists_finite_smoothing_charts
  exists_lipschitzOn_nhds_of_contMDiffAt
  exists_radius_normalizedConvolution_dist_lt_uniform
  normalizedConvolution
  normalizedConvolution_contDiff
  normalizedSmoothChart
  normalizedSmoothChart_contMDiffOn
  normalizedSmoothChart_exists_lipschitz_ball
  normalizedSmoothChart_mfderiv_apply
  normalizedSmoothChart_source
  supportedChartSmoothing
  supportedChartSmoothingHomotopy
  supportedChartSmoothing_eventuallyEq
  supportedChartSmoothing_of_mem)
end PoincareMT.M40

namespace PoincareMT.M40.Topology
export PoincareMT.SurgeryComparison.Topology (
  exists_pos_uniform_mapsTo_of_edist_lt
  homotopicRel_of_nullhomotopic_boundary_trace)
end PoincareMT.M40.Topology

namespace PoincareMT.Proofs.M40
export PoincareMT.SurgeryComparison.Transport (
  chartPerturb
  chartPerturb_eq_of_zero
  chartPerturb_eventuallyEq
  chartPerturb_of_mem
  chartSmoothingDisplacement
  contMDiffAt_chartPerturb_of_mem
  contMDiffAt_supportedChartSmoothing_of_contMDiffAt
  contMDiffAt_supportedChartSmoothing_of_eventuallyEq_one
  continuous_supportedChartSmoothing
  cutoffBlend
  cutoffBlend_dist_le
  eventually_norm_mfderiv_lt
  exists_finite_smoothing_charts
  exists_lipschitzOn_nhds_of_contMDiffAt
  exists_radius_normalizedConvolution_dist_lt_uniform
  normalizedConvolution
  normalizedConvolution_contDiff
  normalizedSmoothChart
  normalizedSmoothChart_contMDiffOn
  normalizedSmoothChart_exists_lipschitz_ball
  normalizedSmoothChart_mfderiv_apply
  normalizedSmoothChart_source
  supportedChartSmoothing
  supportedChartSmoothingHomotopy
  supportedChartSmoothing_eventuallyEq
  supportedChartSmoothing_of_mem)
end PoincareMT.Proofs.M40

namespace PoincareMT.Proofs.M40.Topology
export PoincareMT.SurgeryComparison.Topology (
  exists_pos_uniform_mapsTo_of_edist_lt
  homotopicRel_of_nullhomotopic_boundary_trace)
end PoincareMT.Proofs.M40.Topology

namespace PoincareMT.Proofs.M40
export PoincareMT.SurgeryComparison.Topology (
  exists_pos_uniform_mapsTo_of_edist_lt
  homotopicRel_of_nullhomotopic_boundary_trace)
end PoincareMT.Proofs.M40
