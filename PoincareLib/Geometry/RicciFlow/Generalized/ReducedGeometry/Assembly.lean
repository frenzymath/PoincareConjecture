import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Assembly
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.Construction.ExponentialConclusion
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Regularity.Formulas.ActionValue
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Regularity.Formulas.RegularFormula
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Regularity.PositiveStart.PositiveStartCorrection
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Regularity.Lipschitz.LocalLipschitz
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Measure.Transport.SourceCoverageAssembly
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Rescaling.Geometry.Rescaling
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Ordinary.Capture.OrdinaryCapture

/-!
# Exact generalized L-geometry assembly with the small-time input

Morgan-Tian Sections 6.1-6.7 and Chapter 7, pp. 105-167, and Theorem
8.1, pp. 169-171. Every field uses the actual constructed supplier.
The remaining compact small-time coverage statement is retained
explicitly here and must be proved before the numbered assembly.
-/

set_option autoImplicit false

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval}

/-- Assemble all exact generalized clauses from the actual suppliers
and the explicit compact small-time theorem, Chapters 6-7, pp. 105-167,
and Theorem 8.1, pp. 169-171. -/
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

end PoincareMT.M14
