import PoincareConjecture.Proofs.M11.HorizontalBundle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

theorem box_metric_smooth {time : X → ℝ} {I : SpacetimeInterval}
    (b : AdaptedMetricBox n X time I) :
    ContMDiff (spacetimeModel n)
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) ∞
      (fun q : boxDomain b ↦ b.metric (q.1.val, q.2.val)) := by
  rw [← contMDiffOn_univ]
  exact b.metric_smooth.contMDiffOn.comp
    ((box_time_smooth b).prodMk_space (box_space_smooth b)).contMDiffOn
    (fun q _ ↦ ⟨q.1.property, q.2.property⟩)

noncomputable def horizontalBoxMetric (A : AdaptedMetricAtlas n X)
    (b : A.box_index) (p : X) (hp : p ∈ boxTarget A b) :
    adaptedHorizontal A p →L[ℝ] adaptedHorizontal A p →L[ℝ] ℝ :=
  let q := (boxHomeomorph (A.box b)).symm p
  ((A.box b).metric (q.1.val, q.2.val)).bilinearComp
    (boxHorizontalEquiv A b p hp).symm.toContinuousLinearMap
    (boxHorizontalEquiv A b p hp).symm.toContinuousLinearMap

theorem horizontalBoxMetric_apply (A : AdaptedMetricAtlas n X)
    (b : A.box_index) (p : X) (hp : p ∈ boxTarget A b)
    (v w : adaptedHorizontal A p) :
    horizontalBoxMetric A b p hp v w =
      (A.box b).metric (((boxHomeomorph (A.box b)).symm p).1.val,
        ((boxHomeomorph (A.box b)).symm p).2.val)
        ((boxHorizontalEquiv A b p hp).symm v)
        ((boxHorizontalEquiv A b p hp).symm w) := rfl

theorem horizontalBoxMetric_overlap (A : AdaptedMetricAtlas n X)
    (b c : A.box_index) (p : X) (hb : p ∈ boxTarget A b) (hc : p ∈ boxTarget A c) :
    horizontalBoxMetric A b p hb = horizontalBoxMetric A c p hc := by
  let q := (boxHomeomorph (A.box b)).symm p
  have hq : (A.box b).toSpacetime q ∈ (boxHomeomorph (A.box c)).target := by
    rw [boxHomeomorph_right_inv (A.box b) hb]
    exact hc
  obtain ⟨T⟩ := box_transition_data A b c q hq
  have hcoords := box_transition_eventually_eq (A.box b) (A.box c) q T
  have hderiv : horizontalCoordChange A b c p =
      fderiv ℝ T.coordinateChange q.2.val :=
    boxSpatialTransition_eq A b c q hq T.coordinateChange
      (T.smooth.contDiffAt (T.coordinateChange.open_source.mem_nhds T.source_mem))
      (hcoords.mono fun _ h ↦ h.2)
  have hvector (v : adaptedHorizontal A p) :
      (boxHorizontalEquiv A c p hc).symm v =
        fderiv ℝ T.coordinateChange q.2.val ((boxHorizontalEquiv A b p hb).symm v) := by
    rw [← hderiv, horizontalCoordChange_apply A b c p ⟨hb, hc⟩]
    rw [ContinuousLinearEquiv.apply_symm_apply]
  have htime : q.1.val = ((boxHomeomorph (A.box c)).symm p).1.val :=
    (boxHomeomorph_inverse_time (A.box b) hb).trans
      (boxHomeomorph_inverse_time (A.box c) hc).symm
  have hspace : T.coordinateChange q.2.val =
      ((boxHomeomorph (A.box c)).symm p).2.val := by
    exact T.map_marked.trans (congrArg
      (fun x ↦ ((boxHomeomorph (A.box c)).symm x).2.val)
      (boxHomeomorph_right_inv (A.box b) hb))
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  rw [horizontalBoxMetric_apply, horizontalBoxMetric_apply, hvector, hvector]
  have h := T.metric_eq q.1.val T.time_mem q.2.val T.source_mem
    ((boxHorizontalEquiv A b p hb).symm v) ((boxHorizontalEquiv A b p hb).symm w)
  rw [hspace] at h
  exact h.trans (congrArg (fun t ↦ (A.box c).metric
    (t, ((boxHomeomorph (A.box c)).symm p).2.val)
    (fderiv ℝ T.coordinateChange q.2.val ((boxHorizontalEquiv A b p hb).symm v))
    (fderiv ℝ T.coordinateChange q.2.val ((boxHorizontalEquiv A b p hb).symm w))) htime)

noncomputable def adaptedHorizontalMetric (A : AdaptedMetricAtlas n X) (p : X) :
    adaptedHorizontal A p →L[ℝ] adaptedHorizontal A p →L[ℝ] ℝ :=
  horizontalBoxMetric A (box_targets_cover A p).choose p (box_targets_cover A p).choose_spec

theorem adaptedHorizontalMetric_box (A : AdaptedMetricAtlas n X)
    (b : A.box_index) (p : X) (hp : p ∈ boxTarget A b) :
    adaptedHorizontalMetric A p = horizontalBoxMetric A b p hp :=
  horizontalBoxMetric_overlap A _ b p _ hp

theorem adaptedHorizontalMetric_symm (A : AdaptedMetricAtlas n X) (p : X)
    (v w : adaptedHorizontal A p) :
    adaptedHorizontalMetric A p v w = adaptedHorizontalMetric A p w v := by
  obtain ⟨b, hp⟩ := box_targets_cover A p
  rw [adaptedHorizontalMetric_box A b p hp, horizontalBoxMetric_apply,
    horizontalBoxMetric_apply]
  exact (A.box b).metric_symm _ ((boxHomeomorph (A.box b)).symm p).1.property
    _ ((boxHomeomorph (A.box b)).symm p).2.property _ _

theorem adaptedHorizontalMetric_pos (A : AdaptedMetricAtlas n X) (p : X)
    (v : adaptedHorizontal A p) (hv : v ≠ 0) :
    0 < adaptedHorizontalMetric A p v v := by
  obtain ⟨b, hp⟩ := box_targets_cover A p
  rw [adaptedHorizontalMetric_box A b p hp, horizontalBoxMetric_apply]
  apply (A.box b).metric_pos _ ((boxHomeomorph (A.box b)).symm p).1.property
    _ ((boxHomeomorph (A.box b)).symm p).2.property
  exact fun h ↦ hv ((boxHorizontalEquiv A b p hp).symm.injective (h.trans (map_zero _).symm))

end PoincareConjecture.Proofs.M11
