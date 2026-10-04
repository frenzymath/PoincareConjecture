import PoincareLib.Geometry.Spacetime.Realization.Cylinder.Operations
import PoincareLib.Geometry.Spacetime.Realization.Horizontal.Bracket
import PoincareLib.Geometry.Spacetime.Realization.Slice.Label.Identification
import PoincareLib.Geometry.Spacetime.Realization.Box.CylinderMetric
import PoincareLib.Geometry.Spacetime.GeometryTheory
import PoincareLib.Geometry.Spacetime.Realization.Conclusion

/-!
# Assembly of the generalized-flow carrier conclusion
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

open PoincareMT

namespace Poincare.Spacetime.Realization

noncomputable def adaptedCarrierConclusion {n : ℕ} {X : Type u} [TopologicalSpace X]
    [T2Space X] [SecondCountableTopology X] (A : AdaptedMetricAtlas n X) :
    GeneralizedFlowCarrierConclusionWithInterval A where
  timeIntervals := intervalSystem
  interval_localDiffeomorph := intervalInclusion_localDiffeomorph
  spacetime := adaptedSpacetime A
  slices := adaptedSliceGeometry A
  boxCylinder := adaptedBoxCylinder A
  boxCylinder_eq := fun _ _ ↦ rfl
  box_localDiffeomorph := adapted_box_localDiffeomorph A
  boxMetric := fun b ↦ pulledCylinderMetric (adaptedBoxCylinder A b)
  boxMetric_eq := adaptedBox_metric_eq A
  sliceBox := fun b t ht ↦ sliceBoxMap (A.box b) t ht
  sliceBox_eq := fun _ _ _ _ ↦ rfl
  sliceBox_localDiffeomorph := adapted_sliceBox_localDiffeomorph A
  sliceBox_metric := adapted_sliceBox_metric A
  supplied_labels := fun L t ↦ ⟨adaptedSliceIdentification A L t⟩
  horizontalBracket := spacetime_horizontalBracket (adaptedSpacetime A)
  compatible := adaptedCompatibleTheory.{u, u} A
  coordinate_compatible := adaptedCompatibleTheory.{u, 0} A

end Poincare.Spacetime.Realization
