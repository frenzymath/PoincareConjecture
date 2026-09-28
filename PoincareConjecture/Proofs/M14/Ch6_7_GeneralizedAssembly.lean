import PoincareConjecture.Proofs.M14.PathCalculus
import PoincareConjecture.Proofs.M14.Sec6_3_ExponentialConclusion
import PoincareConjecture.Proofs.M14.Sec6_5_ActionValue
import PoincareConjecture.Proofs.M14.Sec6_5_RegularFormula
import PoincareConjecture.Proofs.M14.Sec6_5_PositiveStartCorrection
import PoincareConjecture.Proofs.M14.Sec6_5_LocalLipschitz
import PoincareConjecture.Proofs.M14.Sec6_7_SourceCoverageAssembly
import PoincareConjecture.Proofs.M14.Sec6_6_Rescaling
import PoincareConjecture.Proofs.M14.OrdinaryCapture










set_option autoImplicit false

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval}




theorem generalizedLGeometryConclusion_of_smallTimeCoverage
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0})
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hM13 : GeneralizedParabolicRescalingTheory.{u} n)
    (G : GeneralizedLGeometryTransport n X time I)
    (hsmall : M14SmallTimeCoverageStatement G) : GeneralizedLGeometryConclusion G where
  path_calculus := pathCalculusConclusion hCoordinates hM04 hM12
  exponential := exponentialConclusion hCoordinates hM04 hM12
  finite_value := finiteValueStatement G
  attainment := attainmentStatement G
  regular_formulas := regularFormulaStatement hCoordinates hM04 hM12 G
  positive_start_correction := positiveStartCorrectionStatement hCoordinates hM04 hM12 G
  measure_transport := measureTransportStatement G
  reduced_volume := reducedVolumeStatement hCoordinates hM04 hM12 G
  local_lipschitz := localLipschitzStatement hCoordinates hM04 hM12 G
  small_time_coverage := hsmall
  reduced_volume_analytic := fun _ _ _ E H =>
    reducedVolumeAnalyticData hCoordinates hM04 hM12 E H
  reduced_volume_source :=
    reducedVolumeSourceCoverageData_of_smallTimeCoverage hCoordinates hM04 hM12 hsmall
  analytic_rescaling := analyticRescalingConclusion hCoordinates hM04 hM12 hM13 G
  ordinary_capture := ordinaryCaptureStatement
    (hM12.gauges X time I G.spacetime G.slices G.timeIntervals G.gaugeCover G.leafwise)
    (pathCalculusConclusion hCoordinates hM04 hM12)

end PoincareConjecture.M14
