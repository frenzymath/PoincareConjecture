import PoincareConjecture.Proofs.M11.BoxMetric
import PoincareConjecture.Proofs.M11.HorizontalInclusion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle ContinuousLinearMap
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

theorem horizontal_trivializationAt (A : AdaptedMetricAtlas n X) (p : X) :
    letI := adaptedHorizontalTopology A
    letI := adaptedHorizontalFiberBundle A
    trivializationAt (EuclideanSpace ℝ (Fin n)) (fun p ↦ adaptedHorizontal A p) p =
      horizontalTrivialization A (box_targets_cover A p).choose := rfl

theorem horizontalTrivialization_symmL (A : AdaptedMetricAtlas n X) (b : A.box_index)
    (p : X) (hp : p ∈ boxTarget A b) (v : EuclideanSpace ℝ (Fin n)) :
    letI := adaptedHorizontalTopology A
    letI := adaptedHorizontalFiberBundle A
    letI := adaptedHorizontalVectorBundle A
    letI := horizontalTrivialization_mem A b
    (horizontalTrivialization A b).symmL ℝ p v = boxHorizontalEquiv A b p hp v := by
  let := adaptedHorizontalTopology A
  let := adaptedHorizontalFiberBundle A
  let := adaptedHorizontalVectorBundle A
  let := horizontalTrivialization_mem A b
  rw [Trivialization.symmL_apply _ hp]
  exact linearPretrivialization_symm (boxTarget A b)
    (fun p hp ↦ (boxHorizontalEquiv A b p hp).symm) p hp v

theorem adaptedHorizontalMetric_smooth (A : AdaptedMetricAtlas n X) :
    letI := adaptedChartedSpace A
    letI := adaptedHorizontalTopology A
    letI := adaptedHorizontalFiberBundle A
    letI := adaptedHorizontalVectorBundle A
    letI := adaptedHorizontalSmoothBundle A
    ContMDiff (spacetimeModel n)
      ((spacetimeModel n).prod
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) ∞
      (fun p ↦ TotalSpace.mk' (EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (E := fun p ↦ adaptedHorizontal A p →L[ℝ] adaptedHorizontal A p →L[ℝ] ℝ)
        p (adaptedHorizontalMetric A p)) := by
  let := adaptedChartedSpace A
  let := adaptedHorizontalTopology A
  let := adaptedHorizontalFiberBundle A
  let := adaptedHorizontalVectorBundle A
  let := adaptedHorizontalSmoothBundle A
  intro p₀
  let b := (box_targets_cover A p₀).choose
  have hb : p₀ ∈ boxTarget A b := (box_targets_cover A p₀).choose_spec
  let := intervalChartedSpace (A.box b).interval
  let := horizontalTrivialization_mem A b
  have hlocal := (box_metric_smooth (A.box b)).contMDiffAt.comp p₀
    ((box_inverse_smooth A b).contMDiffAt ((boxTarget A b).isOpen.mem_nhds hb))
  rw [contMDiffAt_section]
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [(boxTarget A b).isOpen.mem_nhds hb] with p hp
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  rw [hom_trivializationAt_apply]
  simp only [inCoordinates, comp_apply]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ _
    (show p ∈ (trivializationAt
      (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (fun p ↦ adaptedHorizontal A p →L[ℝ] ℝ) p₀).baseSet from
        ⟨by rw [horizontal_trivializationAt]; exact hp, mem_univ p⟩)]
  rw [hom_trivializationAt_apply]
  simp only [inCoordinates, comp_apply]
  simp only [horizontal_trivializationAt]
  change (trivializationAt ℝ (fun _ : X ↦ ℝ) p₀).continuousLinearMapAt ℝ p
      (adaptedHorizontalMetric A p
        ((horizontalTrivialization A b).symmL ℝ p v)
        ((horizontalTrivialization A b).symmL ℝ p w)) = _
  rw [horizontalTrivialization_symmL A b p hp, horizontalTrivialization_symmL A b p hp,
    adaptedHorizontalMetric_box A b p hp, horizontalBoxMetric_apply]
  simp

end PoincareConjecture.Proofs.M11
