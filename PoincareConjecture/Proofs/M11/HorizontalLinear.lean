import PoincareConjecture.Proofs.M11.KernelLinear
import PoincareConjecture.Proofs.M11.TimeVector

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

noncomputable abbrev adaptedHorizontal (A : AdaptedMetricAtlas n X) (p : X) :
    Submodule ℝ (SpacetimeModelVector n) :=
  letI := adaptedChartedSpace A
  spacetimeHorizontal (n := n) A.time p

noncomputable def boxTangentEquiv (A : AdaptedMetricAtlas n X) (b : A.box_index)
    (q : boxDomain (A.box b)) : SpacetimeModelVector n ≃L[ℝ] SpacetimeModelVector n :=
  letI := intervalChartedSpace (A.box b).interval
  letI := adaptedChartedSpace A
  (adapted_box_localDiffeomorph A b).mfderivToContinuousLinearEquiv (by simp) q

theorem boxTangentEquiv_apply (A : AdaptedMetricAtlas n X) (b : A.box_index)
    (q : boxDomain (A.box b)) (v : SpacetimeModelVector n) :
    letI := intervalChartedSpace (A.box b).interval
    letI := adaptedChartedSpace A
    boxTangentEquiv A b q v =
      mfderiv (spacetimeModel n) (spacetimeModel n) (A.box b).toSpacetime q v := rfl

theorem box_time_chain (A : AdaptedMetricAtlas n X) (b : A.box_index)
    (q : boxDomain (A.box b)) (v : SpacetimeModelVector n) :
    letI := adaptedChartedSpace A
    mfderiv (spacetimeModel n) 𝓘(ℝ) A.time ((A.box b).toSpacetime q)
        (boxTangentEquiv A b q v) =
      (smoothInterval (A.box b).interval).inclusionDerivative q.1 v.1 := by
  let := intervalChartedSpace (A.box b).interval
  let := adaptedChartedSpace A
  have hchain := mfderiv_comp_apply q
    ((adapted_time_smooth A ((A.box b).toSpacetime q)).mdifferentiableAt (by simp))
    (((adapted_box_localDiffeomorph A b).contMDiff q).mdifferentiableAt (by simp)) v
  have heq : A.time ∘ (A.box b).toSpacetime = (fun q : boxDomain (A.box b) ↦ q.1.val) :=
    funext (A.box b).time_toSpacetime
  rw [heq, box_time_mfderiv] at hchain
  exact hchain.symm

noncomputable def boxHorizontalEquiv (A : AdaptedMetricAtlas n X) (b : A.box_index)
    (p : X) (hp : p ∈ (boxHomeomorph (A.box b)).target) :
    EuclideanSpace ℝ (Fin n) ≃L[ℝ] adaptedHorizontal A p := by
  letI := adaptedChartedSpace A
  let q := (boxHomeomorph (A.box b)).symm p
  refine spatialKernelEquiv (boxTangentEquiv A b q)
    (mfderiv (spacetimeModel n) 𝓘(ℝ) A.time p)
    ((smoothInterval (A.box b).interval).inclusionDerivative q.1) ?_
  intro v
  have h := box_time_chain A b q v
  rw [boxHomeomorph_right_inv (A.box b) hp] at h
  exact h

theorem boxHorizontalEquiv_apply (A : AdaptedMetricAtlas n X) (b : A.box_index)
    (p : X) (hp : p ∈ (boxHomeomorph (A.box b)).target)
    (v : EuclideanSpace ℝ (Fin n)) :
    (boxHorizontalEquiv A b p hp v).val =
      boxTangentEquiv A b ((boxHomeomorph (A.box b)).symm p) (0, v) := rfl

theorem boxHorizontalEquiv_symm_apply (A : AdaptedMetricAtlas n X) (b : A.box_index)
    (p : X) (hp : p ∈ (boxHomeomorph (A.box b)).target) (v : adaptedHorizontal A p) :
    (boxHorizontalEquiv A b p hp).symm v =
      ((boxTangentEquiv A b ((boxHomeomorph (A.box b)).symm p)).symm v.val).2 := rfl

noncomputable def adaptedHorizontalProjection (A : AdaptedMetricAtlas n X) (p : X) :
    SpacetimeModelVector n →L[ℝ] adaptedHorizontal A p :=
  letI := adaptedChartedSpace A
  normalizedKernelProjection (G := SpacetimeModelVector n)
    (mfderiv (spacetimeModel n) 𝓘(ℝ) A.time p)
    (adaptedTimeVector A p) (adaptedTimeVector_normalized A p)

theorem adaptedHorizontalProjection_eq (A : AdaptedMetricAtlas n X) (p : X)
    (v : SpacetimeModelVector n) :
    letI := adaptedChartedSpace A
    (adaptedHorizontalProjection A p v).val =
      v - (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) A.time p v) •
        (show SpacetimeModelVector n from adaptedTimeVector A p) := rfl

theorem adaptedHorizontalProjection_identity (A : AdaptedMetricAtlas n X) (p : X)
    (v : adaptedHorizontal A p) : adaptedHorizontalProjection A p v.val = v := by
  apply normalizedKernelProjection_identity

theorem adapted_tangent_decomposition (A : AdaptedMetricAtlas n X) (p : X)
    (v : SpacetimeModelVector n) :
    letI := adaptedChartedSpace A
    v = (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) A.time p v) •
      (show SpacetimeModelVector n from adaptedTimeVector A p) +
      (adaptedHorizontalProjection A p v).val := by
  apply normalizedKernelProjection_decomposition

end PoincareConjecture.Proofs.M11
