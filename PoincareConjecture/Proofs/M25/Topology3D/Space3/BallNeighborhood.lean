import PoincareConjecture.Proofs.M25.Topology3D.Space3.CompactChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallExterior
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Geometry.Manifold.Diffeomorph











set_option autoImplicit false

open Set Metric
open scoped ContDiff

namespace PoincareConjecture.M25.Topology3D

variable (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]



structure BallNeighborhoodChart where
  chart : OpenPartialHomeomorph E F
  closedBall_subset_source : closedBall 0 1 ⊆ chart.source
  smooth : ContDiffOn ℝ ∞ chart chart.source
  smooth_symm : ContDiffOn ℝ ∞ chart.symm chart.target

namespace BallNeighborhoodChart

variable {E F} (B : BallNeighborhoodChart E F)


def inside : Set F := B.chart '' ball 0 1


def closedRegion : Set F := B.chart '' closedBall 0 1


def boundary : Set F := B.chart '' sphere 0 1


theorem inside_open : IsOpen B.inside :=
  B.chart.isOpen_image_of_subset_source isOpen_ball
    (ball_subset_closedBall.trans B.closedBall_subset_source)


theorem inside_connected : IsConnected B.inside := by
  exact (convex_ball (0 : E) (1 : ℝ)).isConnected (nonempty_ball.mpr zero_lt_one) |>.image
    B.chart (B.chart.continuousOn.mono
      (ball_subset_closedBall.trans B.closedBall_subset_source))


theorem inside_disjoint_boundary : Disjoint B.inside B.boundary := by
  apply Set.disjoint_left.mpr
  rintro y ⟨x, hx, rfl⟩ ⟨z, hz, heq⟩
  have hzx := B.chart.injOn
    (B.closedBall_subset_source (sphere_subset_closedBall hz))
    (B.closedBall_subset_source (ball_subset_closedBall hx)) heq
  subst z
  exact (ne_of_lt (mem_ball_zero_iff.mp hx)) (mem_sphere_zero_iff_norm.mp hz)

variable [ProperSpace E]


theorem exists_larger_ball : ∃ R : ℝ, 1 < R ∧ ball 0 R ⊆ B.chart.source := by
  obtain ⟨d, hd, hsub⟩ := (isCompact_closedBall (0 : E) 1).exists_thickening_subset_open
    B.chart.open_source B.closedBall_subset_source
  rw [thickening_closedBall hd zero_le_one] at hsub
  exact ⟨d + 1, by linarith, hsub⟩


theorem closedRegion_compact : IsCompact B.closedRegion :=
  (isCompact_closedBall (0 : E) 1).image_of_continuousOn
    (B.chart.continuousOn.mono B.closedBall_subset_source)


theorem inside_bounded : Bornology.IsBounded B.inside :=
  B.closedRegion_compact.isBounded.subset (image_mono ball_subset_closedBall)


theorem closure_inside : closure B.inside = B.closedRegion :=
  compactChart_closure_ball B.chart 0 zero_lt_one B.closedBall_subset_source


theorem frontier_inside : frontier B.inside = B.boundary :=
  compactChart_frontier_ball B.chart 0 zero_lt_one B.closedBall_subset_source

omit [ProperSpace E] in

theorem inside_union_boundary : B.inside ∪ B.boundary = B.closedRegion := by
  change B.chart '' ball 0 1 ∪ B.chart '' sphere 0 1 = B.chart '' closedBall 0 1
  rw [← image_union, ball_union_sphere]



theorem outside_connected (hdim : 1 < Module.rank ℝ E) :
    IsConnected (univ \ (B.inside ∪ B.boundary)) := by
  obtain ⟨R, hR, hsub⟩ := B.exists_larger_ball
  rw [B.inside_union_boundary, ← compl_eq_univ_sdiff]
  exact compactChart_exterior_connected B.chart hdim hR hsub

end BallNeighborhoodChart
end PoincareConjecture.M25.Topology3D
