import PoincareConjecture.Proofs.M11.BoxCylinder
import PoincareConjecture.Proofs.M11.CylinderMetric





set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]

theorem adaptedBox_spatialEquiv (A : AdaptedMetricAtlas n X) (b : A.box_index)
    (t : (smoothInterval (A.box b).interval).Point) (x : (A.box b).spatial)
    (v : EuclideanSpace ℝ (Fin n)) :
    cylinderSpatialEquiv (adaptedBoxCylinder A b) t x v =
      boxHorizontalEquiv A b ((A.box b).toSpacetime (t, x))
        ((boxHomeomorph (A.box b)).map_source (Set.mem_univ (t, x))) v := by
  apply Subtype.ext
  rw [cylinderSpatialEquiv_apply, boxHorizontalEquiv_apply, boxHomeomorph_left_inv]
  rfl

theorem adaptedBox_metric_eq (A : AdaptedMetricAtlas n X) (b : A.box_index)
    (t : (smoothInterval (A.box b).interval).Point) (x : (A.box b).spatial)
    (v w : EuclideanSpace ℝ (Fin n)) :
    ((pulledCylinderMetric (adaptedBoxCylinder A b)).metric t.val).inner x v w =
      (A.box b).metric (t.val, x) v w := by
  change cylinderMetricForm (adaptedBoxCylinder A b)
    (cylinderMetricTime (A.box b).interval t.val) x v w = _
  rw [cylinderMetricTime_of_mem]
  change adaptedHorizontalMetric A ((A.box b).toSpacetime (t, x))
    (cylinderSpatialEquiv (adaptedBoxCylinder A b) t x v)
    (cylinderSpatialEquiv (adaptedBoxCylinder A b) t x w) = _
  rw [adaptedBox_spatialEquiv, adaptedBox_spatialEquiv]
  rw [adaptedHorizontalMetric_box A b ((A.box b).toSpacetime (t, x))
    ((boxHomeomorph (A.box b)).map_source (Set.mem_univ (t, x)))]
  rw [horizontalBoxMetric_apply, ContinuousLinearEquiv.symm_apply_apply,
    ContinuousLinearEquiv.symm_apply_apply, boxHomeomorph_left_inv]

end PoincareConjecture.Proofs.M11
