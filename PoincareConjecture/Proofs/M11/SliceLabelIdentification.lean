import PoincareConjecture.Proofs.M11.SliceLabelSmooth
import PoincareConjecture.Proofs.M11.SliceBoxMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

theorem sliceLabelDiffeomorph_box_derivative (A : AdaptedMetricAtlas n X)
    (L : SpacetimeSliceLabeling A) (b : A.box_index) (t : ℝ)
    (ht : t ∈ (A.box b).interval.domain) (x : (A.box b).spatial)
    (v : EuclideanSpace ℝ (Fin n)) :
    letI := adaptedSliceChartedSpace A t
    mfderiv (𝓡 n) (𝓡 n) (sliceLabelDiffeomorph A L t) (L.boxMap b t ht x)
        (labelBoxTangentEquiv A L b t ht x v) =
      sliceBoxTangentEquiv A b t ht x v := by
  let := adaptedSliceChartedSpace A t
  have h := mfderiv_comp_apply x
    (((sliceLabelDiffeomorph A L t).contMDiff (L.boxMap b t ht x)).mdifferentiableAt (by simp))
    ((L.boxMap_smooth b t ht x).mdifferentiableAt (by simp)) v
  have heq : (sliceLabelDiffeomorph A L t) ∘ L.boxMap b t ht =
      sliceBoxMap (A.box b) t ht := funext (sliceLabelHomeomorph_box A L b t ht)
  rw [heq] at h
  exact h.symm

theorem sliceLabel_metric_box (A : AdaptedMetricAtlas n X)
    (L : SpacetimeSliceLabeling A) (b : A.box_index) (t : ℝ)
    (ht : t ∈ (A.box b).interval.domain) (x : (A.box b).spatial)
    (v w : EuclideanSpace ℝ (Fin n)) :
    letI := adaptedSliceChartedSpace A t
    sliceMetricForm A t (sliceLabelDiffeomorph A L t (L.boxMap b t ht x))
        (mfderiv (𝓡 n) (𝓡 n) (sliceLabelDiffeomorph A L t) (L.boxMap b t ht x)
          (labelBoxTangentEquiv A L b t ht x v))
        (mfderiv (𝓡 n) (𝓡 n) (sliceLabelDiffeomorph A L t) (L.boxMap b t ht x)
          (labelBoxTangentEquiv A L b t ht x w)) =
      (L.slice t).metric.inner (L.boxMap b t ht x)
        (labelBoxTangentEquiv A L b t ht x v) (labelBoxTangentEquiv A L b t ht x w) := by
  let := adaptedSliceChartedSpace A t
  rw [sliceLabelDiffeomorph_box_derivative, sliceLabelDiffeomorph_box_derivative]
  have hp : sliceLabelDiffeomorph A L t (L.boxMap b t ht x) =
      sliceBoxMap (A.box b) t ht x := sliceLabelHomeomorph_box A L b t ht x
  rw [hp, sliceMetricForm_box]
  exact (L.metric_eq b t ht x v w).symm

theorem sliceLabel_metric (A : AdaptedMetricAtlas n X)
    (L : SpacetimeSliceLabeling A) (t : ℝ) (p : (L.slice t).carrier)
    (v w : EuclideanSpace ℝ (Fin n)) :
    letI := adaptedSliceChartedSpace A t
    sliceMetricForm A t (sliceLabelDiffeomorph A L t p)
        (mfderiv (𝓡 n) (𝓡 n) (sliceLabelDiffeomorph A L t) p v)
        (mfderiv (𝓡 n) (𝓡 n) (sliceLabelDiffeomorph A L t) p w) =
      (L.slice t).metric.inner p v w := by
  let := adaptedSliceChartedSpace A t
  obtain ⟨b, hp⟩ := labelBox_targets_cover A L t p
  let x := (labelBoxHomeomorph A L b.val t b.property).symm p
  have heq : L.boxMap b.val t b.property x = p :=
    (labelBoxHomeomorph_apply A L b.val t b.property x).symm.trans
      ((labelBoxHomeomorph A L b.val t b.property).right_inv hp)
  have h := sliceLabel_metric_box A L b.val t b.property x
    ((labelBoxTangentEquiv A L b.val t b.property x).symm v)
    ((labelBoxTangentEquiv A L b.val t b.property x).symm w)
  simp only [ContinuousLinearEquiv.apply_symm_apply] at h
  exact heq ▸ h

noncomputable def adaptedSliceIdentification [T2Space X] [SecondCountableTopology X]
    (A : AdaptedMetricAtlas n X) (L : SpacetimeSliceLabeling A) (t : ℝ) :
    SpacetimeSliceIdentification (adaptedSpacetime A) t (adaptedSliceGeometry A t) (L.slice t) where
  identification := sliceLabelDiffeomorph A L t
  identification_eq := fun _ ↦ rfl
  tangent_eq := by
    let := adaptedChartedSpace A
    let := adaptedSliceChartedSpace A t
    intro p v
    change (sliceHorizontalEquiv A t (sliceLabelDiffeomorph A L t p)
      (mfderiv (𝓡 n) (𝓡 n) (sliceLabelDiffeomorph A L t) p v)).val = _
    rw [sliceHorizontalEquiv_eq]
    exact (mfderiv_comp_apply p
      ((slice_inclusion_smooth A t (sliceLabelDiffeomorph A L t p)).mdifferentiableAt (by simp))
      (((sliceLabelDiffeomorph A L t).contMDiff p).mdifferentiableAt (by simp)) v).symm
  metric_eq := sliceLabel_metric A L t
  measurable := by
    let := adaptedSliceChartedSpace A t
    let : MeasurableSpace (spacetimeSlice A.time t) :=
      (adaptedSliceGeometry A t).measurableSpace
    let : BorelSpace (spacetimeSlice A.time t) := (adaptedSliceGeometry A t).borelSpace
    exact ⟨(sliceLabelDiffeomorph A L t).continuous.measurable,
      (sliceLabelDiffeomorph A L t).symm.continuous.measurable⟩

end PoincareConjecture.Proofs.M11
