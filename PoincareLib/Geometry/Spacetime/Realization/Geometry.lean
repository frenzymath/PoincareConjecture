import PoincareLib.Geometry.Spacetime.Realization.Horizontal.MetricSmooth
import PoincareLib.Geometry.Spacetime.Realization.Bundle.PositiveFormBounded
import PoincareLib.Geometry.Spacetime.Realization.Horizontal.Projection

/-!
# Actual spacetime geometry on the supplied carrier
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle
open scoped Manifold ContDiff Bundle Topology

open PoincareMT

namespace Poincare.Spacetime.Realization

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

noncomputable def adaptedRiemannianMetric (A : AdaptedMetricAtlas n X) :
    letI := adaptedChartedSpace A
    letI := adaptedHorizontalTopology A
    letI := adaptedHorizontalFiberBundle A
    letI := adaptedHorizontalVectorBundle A
    ContMDiffRiemannianMetric (spacetimeModel n) ∞ (EuclideanSpace ℝ (Fin n))
      (fun p ↦ adaptedHorizontal A p) :=
  letI := adaptedChartedSpace A
  letI := adaptedHorizontalTopology A
  letI := adaptedHorizontalFiberBundle A
  letI := adaptedHorizontalVectorBundle A
  {
    inner := adaptedHorizontalMetric A
    symm := adaptedHorizontalMetric_symm A
    pos := adaptedHorizontalMetric_pos A
    isVonNBounded := fun p ↦ positiveForm_isVonNBounded (adaptedHorizontalMetric A p)
      (adaptedHorizontalMetric_pos A p)
    contMDiff := adaptedHorizontalMetric_smooth A
  }

noncomputable def adaptedSpacetime [T2Space X] [SecondCountableTopology X]
    (A : AdaptedMetricAtlas n X) : GeneralizedFlowSpacetime n X A.time A.interval where
  chartedSpace := adaptedChartedSpace A
  isManifold := adapted_isManifold A
  t2Space := inferInstance
  t3Space := adapted_t3Space A
  secondCountable := inferInstance
  time_smooth := adapted_time_smooth A
  time_range := A.time_range
  boundary_eq := adapted_boundary_eq A
  timeVector := adaptedTimeVector A
  timeVector_smooth := adaptedTimeVector_smooth A
  timeVector_normalized := adaptedTimeVector_normalized A
  horizontalTopology := adaptedHorizontalTopology A
  horizontalFiberBundle := adaptedHorizontalFiberBundle A
  horizontalVectorBundle := adaptedHorizontalVectorBundle A
  horizontalSmoothBundle := adaptedHorizontalSmoothBundle A
  horizontal_inclusion_smooth := horizontalInclusion_smooth A
  horizontalProjection := adaptedHorizontalProjection A
  horizontalProjection_eq := adaptedHorizontalProjection_eq A
  horizontalProjection_identity := adaptedHorizontalProjection_identity A
  tangent_decomposition := adapted_tangent_decomposition A
  horizontalProjection_smooth := adaptedHorizontalProjection_smooth A
  metric := adaptedRiemannianMetric A

end Poincare.Spacetime.Realization
