import PoincareConjecture.Proofs.M11.SliceCharts
import PoincareConjecture.Proofs.M11.HorizontalLinear

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

noncomputable def sliceBoxTangentEquiv (A : AdaptedMetricAtlas n X) (b : A.box_index)
    (t : ℝ) (ht : t ∈ (A.box b).interval.domain) (x : (A.box b).spatial) :
    EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  letI := adaptedSliceChartedSpace A t
  (adapted_sliceBox_localDiffeomorph A b t ht).mfderivToContinuousLinearEquiv (by simp) x

theorem slice_inclusion_box_derivative (A : AdaptedMetricAtlas n X) (b : A.box_index)
    (t : ℝ) (ht : t ∈ (A.box b).interval.domain) (x : (A.box b).spatial)
    (v : EuclideanSpace ℝ (Fin n)) :
    letI := adaptedChartedSpace A
    letI := adaptedSliceChartedSpace A t
    mfderiv (𝓡 n) (spacetimeModel n) (Subtype.val : spacetimeSlice A.time t → X)
      (sliceBoxMap (A.box b) t ht x) (sliceBoxTangentEquiv A b t ht x v) =
      boxTangentEquiv A b (⟨t, ht⟩, x) (0, v) := by
  let := intervalChartedSpace (A.box b).interval
  let := adaptedChartedSpace A
  let := adaptedSliceChartedSpace A t
  have hfixed : ContMDiff (𝓡 n) (spacetimeModel n) ∞
      (fun y : (A.box b).spatial ↦ ((⟨t, ht⟩ : (A.box b).interval.domain), y)) :=
    contMDiff_const.prodMk contMDiff_id
  have h₁ := mfderiv_comp_apply x
    ((slice_inclusion_smooth A t (sliceBoxMap (A.box b) t ht x)).mdifferentiableAt (by simp))
    (((adapted_sliceBox_localDiffeomorph A b t ht).contMDiff x).mdifferentiableAt (by simp)) v
  have h₂ := mfderiv_comp_apply x
    (((adapted_box_localDiffeomorph A b).contMDiff (⟨t, ht⟩, x)).mdifferentiableAt (by simp))
    ((hfixed x).mdifferentiableAt (by simp)) v
  rw [mfderiv_prod_right] at h₂
  exact h₁.symm.trans h₂

noncomputable def sliceHorizontalEquivAtBox (A : AdaptedMetricAtlas n X)
    (b : A.box_index) (t : ℝ) (ht : t ∈ (A.box b).interval.domain)
    (p : spacetimeSlice A.time t) (hp : p ∈ (sliceHomeomorph (A.box b) t ht).target) :
    EuclideanSpace ℝ (Fin n) ≃L[ℝ] adaptedHorizontal A p.val :=
  let x := (sliceHomeomorph (A.box b) t ht).symm p
  (sliceBoxTangentEquiv A b t ht x).symm.trans
    (boxHorizontalEquiv A b p.val (by
      rw [sliceHomeomorph_target] at hp
      exact hp))

theorem sliceHorizontalEquivAtBox_eq (A : AdaptedMetricAtlas n X)
    (b : A.box_index) (t : ℝ) (ht : t ∈ (A.box b).interval.domain)
    (p : spacetimeSlice A.time t) (hp : p ∈ (sliceHomeomorph (A.box b) t ht).target)
    (v : EuclideanSpace ℝ (Fin n)) :
    letI := adaptedChartedSpace A
    letI := adaptedSliceChartedSpace A t
    (sliceHorizontalEquivAtBox A b t ht p hp v).val =
      mfderiv (𝓡 n) (spacetimeModel n) (Subtype.val : spacetimeSlice A.time t → X) p v := by
  let := adaptedChartedSpace A
  let := adaptedSliceChartedSpace A t
  let x := (sliceHomeomorph (A.box b) t ht).symm p
  have hpoint : sliceBoxMap (A.box b) t ht x = p :=
    (sliceHomeomorph (A.box b) t ht).right_inv hp
  have hcoords : (boxHomeomorph (A.box b)).symm p.val = (⟨t, ht⟩, x) := by
    have hval := congrArg Subtype.val hpoint
    exact (congrArg (boxHomeomorph (A.box b)).symm hval).symm.trans
      (boxHomeomorph_left_inv (A.box b) (⟨t, ht⟩, x))
  have h := slice_inclusion_box_derivative A b t ht x
    ((sliceBoxTangentEquiv A b t ht x).symm v)
  rw [ContinuousLinearEquiv.apply_symm_apply, hpoint] at h
  have hb : p.val ∈ (boxHomeomorph (A.box b)).target := by
    rw [sliceHomeomorph_target] at hp
    exact hp
  change (boxHorizontalEquiv A b p.val hb
    ((sliceBoxTangentEquiv A b t ht x).symm v)).val = _
  rw [boxHorizontalEquiv_apply, hcoords]
  exact h.symm

noncomputable def sliceHorizontalEquiv (A : AdaptedMetricAtlas n X) (t : ℝ)
    (p : spacetimeSlice A.time t) :
    EuclideanSpace ℝ (Fin n) ≃L[ℝ] adaptedHorizontal A p.val :=
  let b := (slice_targets_cover A t p).choose
  sliceHorizontalEquivAtBox A b.val t b.property p (slice_targets_cover A t p).choose_spec

theorem sliceHorizontalEquiv_eq (A : AdaptedMetricAtlas n X) (t : ℝ)
    (p : spacetimeSlice A.time t) (v : EuclideanSpace ℝ (Fin n)) :
    letI := adaptedChartedSpace A
    letI := adaptedSliceChartedSpace A t
    (sliceHorizontalEquiv A t p v).val =
      mfderiv (𝓡 n) (spacetimeModel n) (Subtype.val : spacetimeSlice A.time t → X) p v :=
  sliceHorizontalEquivAtBox_eq A _ t _ p (slice_targets_cover A t p).choose_spec v

end PoincareConjecture.Proofs.M11
