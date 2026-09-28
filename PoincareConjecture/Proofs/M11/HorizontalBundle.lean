import PoincareConjecture.Proofs.M11.SpatialTransitions
import PoincareConjecture.Proofs.M11.VectorCover





set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

noncomputable def boxTarget (A : AdaptedMetricAtlas n X) (b : A.box_index) :
    TopologicalSpace.Opens X :=
  ⟨(boxHomeomorph (A.box b)).target, (boxHomeomorph (A.box b)).open_target⟩

noncomputable def horizontalCoordChange (A : AdaptedMetricAtlas n X) (b c : A.box_index)
    (p : X) : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  boxSpatialTransition A b c ((boxHomeomorph (A.box b)).symm p)

theorem horizontalCoordChange_smooth (A : AdaptedMetricAtlas n X) (b c : A.box_index) :
    letI := adaptedChartedSpace A
    ContMDiffOn (spacetimeModel n)
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ∞
      (horizontalCoordChange A b c) ((boxTarget A b : Set X) ∩ boxTarget A c) := by
  let := intervalChartedSpace (A.box b).interval
  let := adaptedChartedSpace A
  apply (boxSpatialTransition_smooth A b c).comp
    ((box_inverse_smooth A b).mono inter_subset_left)
  intro p hp
  refine ⟨mem_univ _, ?_⟩
  change (A.box b).toSpacetime ((boxHomeomorph (A.box b)).symm p) ∈
    (boxHomeomorph (A.box c)).target
  rw [boxHomeomorph_right_inv (A.box b) hp.1]
  exact hp.2

theorem horizontalCoordChange_apply (A : AdaptedMetricAtlas n X) (b c : A.box_index)
    (p : X) (hp : p ∈ (boxTarget A b : Set X) ∩ boxTarget A c)
    (v : EuclideanSpace ℝ (Fin n)) :
    horizontalCoordChange A b c p v =
      (boxHorizontalEquiv A c p hp.2).symm (boxHorizontalEquiv A b p hp.1 v) :=
  (boxHorizontalEquiv_transition A b c p hp.1 hp.2 v).symm

noncomputable def adaptedHorizontalPrebundle (A : AdaptedMetricAtlas n X) :
    VectorPrebundle ℝ (EuclideanSpace ℝ (Fin n)) (fun p ↦ adaptedHorizontal A p) :=
  letI := adaptedChartedSpace A
  linearVectorPrebundle (boxTarget A) (fun b p hp ↦ (boxHorizontalEquiv A b p hp).symm)
    (box_targets_cover A) (horizontalCoordChange A)
    (fun b c ↦ (horizontalCoordChange_smooth A b c).continuousOn)
    (horizontalCoordChange_apply A)

theorem adaptedHorizontalPrebundle_smooth (A : AdaptedMetricAtlas n X) :
    letI := adaptedChartedSpace A
    (adaptedHorizontalPrebundle A).IsContMDiff (spacetimeModel n) ∞ := by
  let := adaptedChartedSpace A
  apply linearVectorPrebundle_smooth
  exact horizontalCoordChange_smooth A

noncomputable abbrev adaptedHorizontalTopology (A : AdaptedMetricAtlas n X) :
    TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin n)) (fun p ↦ adaptedHorizontal A p)) :=
  (adaptedHorizontalPrebundle A).totalSpaceTopology

noncomputable abbrev adaptedHorizontalFiberBundle (A : AdaptedMetricAtlas n X) :
    letI := adaptedHorizontalTopology A
    FiberBundle (EuclideanSpace ℝ (Fin n)) (fun p ↦ adaptedHorizontal A p) :=
  (adaptedHorizontalPrebundle A).toFiberBundle

theorem adaptedHorizontalVectorBundle (A : AdaptedMetricAtlas n X) :
    letI := adaptedHorizontalTopology A
    letI := adaptedHorizontalFiberBundle A
    VectorBundle ℝ (EuclideanSpace ℝ (Fin n)) (fun p ↦ adaptedHorizontal A p) :=
  (adaptedHorizontalPrebundle A).toVectorBundle

theorem adaptedHorizontalSmoothBundle (A : AdaptedMetricAtlas n X) :
    letI := adaptedChartedSpace A
    letI := adaptedHorizontalTopology A
    letI := adaptedHorizontalFiberBundle A
    letI := adaptedHorizontalVectorBundle A
    ContMDiffVectorBundle ∞ (EuclideanSpace ℝ (Fin n)) (fun p ↦ adaptedHorizontal A p)
      (spacetimeModel n) := by
  let := adaptedChartedSpace A
  let := adaptedHorizontalTopology A
  let := adaptedHorizontalFiberBundle A
  let := adaptedHorizontalVectorBundle A
  let := adaptedHorizontalPrebundle_smooth A
  exact (adaptedHorizontalPrebundle A).contMDiffVectorBundle (spacetimeModel n)

noncomputable def horizontalTrivialization (A : AdaptedMetricAtlas n X) (b : A.box_index) :
    letI := adaptedHorizontalTopology A
    Trivialization (EuclideanSpace ℝ (Fin n))
      (π (EuclideanSpace ℝ (Fin n)) (fun p ↦ adaptedHorizontal A p)) :=
  (adaptedHorizontalPrebundle A).trivializationOfMemPretrivializationAtlas ⟨b, rfl⟩

theorem horizontalTrivialization_mem (A : AdaptedMetricAtlas n X) (b : A.box_index) :
    letI := adaptedHorizontalTopology A
    letI := adaptedHorizontalFiberBundle A
    MemTrivializationAtlas (horizontalTrivialization A b) := by
  let := adaptedHorizontalTopology A
  let := adaptedHorizontalFiberBundle A
  exact ⟨_, ⟨b, rfl⟩, rfl⟩

end PoincareConjecture.Proofs.M11
