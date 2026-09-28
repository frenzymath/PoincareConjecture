import PoincareConjecture.Proofs.M11.SliceGeometry





set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

theorem sliceHorizontalEquiv_box (A : AdaptedMetricAtlas n X) (b : A.box_index)
    (t : ℝ) (ht : t ∈ (A.box b).interval.domain) (x : (A.box b).spatial)
    (v : EuclideanSpace ℝ (Fin n)) :
    sliceHorizontalEquiv A t (sliceBoxMap (A.box b) t ht x)
        (sliceBoxTangentEquiv A b t ht x v) =
      boxHorizontalEquiv A b ((A.box b).toSpacetime (⟨t, ht⟩, x))
        ((boxHomeomorph (A.box b)).map_source (by simp [boxHomeomorph_source])) v := by
  apply Subtype.ext
  rw [sliceHorizontalEquiv_eq, slice_inclusion_box_derivative,
    boxHorizontalEquiv_apply, boxHomeomorph_left_inv]

theorem sliceMetricForm_box (A : AdaptedMetricAtlas n X) (b : A.box_index)
    (t : ℝ) (ht : t ∈ (A.box b).interval.domain) (x : (A.box b).spatial)
    (v w : EuclideanSpace ℝ (Fin n)) :
    sliceMetricForm A t (sliceBoxMap (A.box b) t ht x)
        (sliceBoxTangentEquiv A b t ht x v) (sliceBoxTangentEquiv A b t ht x w) =
      (A.box b).metric (t, x) v w := by
  change adaptedHorizontalMetric A _
    (sliceHorizontalEquiv A t _ (sliceBoxTangentEquiv A b t ht x v))
    (sliceHorizontalEquiv A t _ (sliceBoxTangentEquiv A b t ht x w)) = _
  rw [sliceHorizontalEquiv_box, sliceHorizontalEquiv_box]
  change adaptedHorizontalMetric A ((A.box b).toSpacetime (⟨t, ht⟩, x)) _ _ = _
  rw [adaptedHorizontalMetric_box A b ((A.box b).toSpacetime (⟨t, ht⟩, x))
    ((boxHomeomorph (A.box b)).map_source (by simp [boxHomeomorph_source]))]
  rw [horizontalBoxMetric_apply, ContinuousLinearEquiv.symm_apply_apply,
    ContinuousLinearEquiv.symm_apply_apply, boxHomeomorph_left_inv]

theorem adapted_sliceBox_metric [T2Space X] [SecondCountableTopology X]
    (A : AdaptedMetricAtlas n X) (b : A.box_index)
    (t : ℝ) (ht : t ∈ (A.box b).interval.domain) (x : (A.box b).spatial)
    (v w : EuclideanSpace ℝ (Fin n)) :
    letI := adaptedSliceChartedSpace A t
    (adaptedSliceGeometry A t).metricOnPoints.inner (sliceBoxMap (A.box b) t ht x)
        (mfderiv (𝓡 n) (𝓡 n) (sliceBoxMap (A.box b) t ht) x v)
        (mfderiv (𝓡 n) (𝓡 n) (sliceBoxMap (A.box b) t ht) x w) =
      (A.box b).metric (t, x) v w :=
  sliceMetricForm_box A b t ht x v w

end PoincareConjecture.Proofs.M11
