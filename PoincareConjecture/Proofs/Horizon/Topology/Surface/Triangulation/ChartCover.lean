


import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.OpenPartialHomeomorph.IsImage













set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface

universe u

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]


theorem exists_chart_closedBall_subset (x : M) :
    ∃ r : ℝ, 0 < r ∧
      closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) r ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).target := by
  exact Metric.nhds_basis_closedBall.mem_iff.mp
    ((chartAt (EuclideanSpace ℝ (Fin 2)) x).open_target.mem_nhds
      ((chartAt (EuclideanSpace ℝ (Fin 2)) x).map_source (mem_chart_source _ x)))


theorem isCompact_chart_closedBall (x : M) {r : ℝ}
    (hr : closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) r ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    IsCompact ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) r) :=
  (isCompact_closedBall _ _).image_of_continuousOn
    ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm.continuousOn.mono hr)


theorem chart_closedBall_subset_source (x : M) {r : ℝ}
    (hr : closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) r ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) r ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).source := by
  rintro _ ⟨y, hy, rfl⟩
  exact (chartAt (EuclideanSpace ℝ (Fin 2)) x).map_target (hr hy)


theorem isOpen_chart_ball (x : M) {r : ℝ}
    (hr : closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) r ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    IsOpen ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      ball (chartAt (EuclideanSpace ℝ (Fin 2)) x x) r) :=
  (chartAt (EuclideanSpace ℝ (Fin 2)) x).isOpen_image_symm_of_subset_target
    isOpen_ball (ball_subset_closedBall.trans hr)


theorem mem_chart_ball (x : M) {r : ℝ} (hr : 0 < r) :
    x ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      ball (chartAt (EuclideanSpace ℝ (Fin 2)) x x) r :=
  ⟨_, mem_ball_self hr, (chartAt (EuclideanSpace ℝ (Fin 2)) x).left_inv
    (mem_chart_source _ x)⟩

private theorem chart_symm_isImage (x : M) {K : Set (EuclideanSpace ℝ (Fin 2))}
    (hK : K ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm.IsImage K
      ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm '' K) := by
  intro y hy
  constructor
  · rintro ⟨z, hz, hzy⟩
    exact ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm.injOn (hK hz) hy hzy) ▸ hz
  · exact mem_image_of_mem _


theorem interior_chart_image (x : M) {K : Set (EuclideanSpace ℝ (Fin 2))}
    (hK : K ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    interior ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm '' K) =
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm '' interior K := by
  have himage : (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm '' K ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).source := by
    rintro _ ⟨z, hz, rfl⟩
    exact (chartAt (EuclideanSpace ℝ (Fin 2)) x).map_target (hK hz)
  simpa only [OpenPartialHomeomorph.symm_source, OpenPartialHomeomorph.symm_target,
    inter_eq_right.mpr (interior_subset.trans hK),
    inter_eq_right.mpr (interior_subset.trans himage)] using
    (chart_symm_isImage x hK).interior.image_eq.symm


theorem frontier_chart_image [T2Space M] (x : M)
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hcompact : IsCompact K)
    (hK : K ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    frontier ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm '' K) =
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm '' frontier K := by
  have himage : (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm '' K ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).source := by
    rintro _ ⟨z, hz, rfl⟩
    exact (chartAt (EuclideanSpace ℝ (Fin 2)) x).map_target (hK hz)
  have hcimage : IsCompact ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm '' K) :=
    hcompact.image_of_continuousOn
      ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm.continuousOn.mono hK)
  simpa only [OpenPartialHomeomorph.symm_source, OpenPartialHomeomorph.symm_target,
    inter_eq_right.mpr (hcompact.isClosed.frontier_subset.trans hK),
    inter_eq_right.mpr (hcimage.isClosed.frontier_subset.trans himage)] using
    (chart_symm_isImage x hK).frontier.image_eq.symm


theorem closure_chart_ball [T2Space M] (x : M) {r : ℝ} (hpos : 0 < r)
    (hr : closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) r ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    closure ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      ball (chartAt (EuclideanSpace ℝ (Fin 2)) x x) r) =
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) r := by
  have hc : IsCompact (closure (ball (chartAt (EuclideanSpace ℝ (Fin 2)) x x) r)) := by
    rw [closure_ball _ hpos.ne']
    exact isCompact_closedBall _ _
  have hcont : ContinuousOn (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm
      (closure (ball (chartAt (EuclideanSpace ℝ (Fin 2)) x x) r)) := by
    rw [closure_ball _ hpos.ne']
    exact (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm.continuousOn.mono hr
  simpa only [closure_ball _ hpos.ne'] using (image_closure_of_isCompact hc hcont).symm



theorem exists_finite_chart_ball_cover [CompactSpace M] :
    ∃ (s : Finset M) (r : M → ℝ),
      (∀ x, 0 < r x) ∧
      (∀ x, closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) (r x) ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) ∧
      (⋃ x ∈ s, (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        ball (chartAt (EuclideanSpace ℝ (Fin 2)) x x) (r x)) = (univ : Set M) := by
  classical
  choose r hpos hsub using exists_chart_closedBall_subset (M := M)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : M => (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      ball (chartAt (EuclideanSpace ℝ (Fin 2)) x x) (r x))
    (fun x => isOpen_chart_ball x (hsub x))
    (by intro x _; exact mem_iUnion.mpr ⟨x, mem_chart_ball x (hpos x)⟩)
  exact ⟨s, r, hpos, hsub, Subset.antisymm (subset_univ _) hs⟩

end PoincareConjecture.Topology.Surface
