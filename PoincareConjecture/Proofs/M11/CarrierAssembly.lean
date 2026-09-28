import PoincareConjecture.Proofs.M11.CompatibleTheory
import PoincareConjecture.Proofs.M11.SpacetimeHorizontalBracket
import PoincareConjecture.Proofs.M11.SliceLabelIdentification
import PoincareConjecture.Proofs.M11.BoxCylinderMetric
import PoincareConjecture.Statements.M11GeneralizedFlow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M11

noncomputable def adaptedCarrierConclusion {n : ℕ} {X : Type u} [TopologicalSpace X]
    [T2Space X] [SecondCountableTopology X] (A : AdaptedMetricAtlas n X) :
    GeneralizedFlowCarrierConclusion A where
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

end PoincareConjecture.Proofs.M11
