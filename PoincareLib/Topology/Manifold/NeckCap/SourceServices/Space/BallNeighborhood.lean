import PoincareLib.Topology.Manifold.NeckCap.SourceServices.Space.CompactChart
import PoincareLib.Topology.Manifold.NeckCap.SourceServices.Space.BallExterior
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Smooth neighborhood certificates for balls

The ball pieces in Hatcher, Notes on Basic 3-Manifold Topology,
Theorem 1.1 and Lemmas 1.2-1.3, pp. 1-3, retain coordinates through
their boundaries. The certificate here records such coordinates and
derives the inside, frontier, and connected exterior from them.
See `derivations/2026-09-21-ball-neighborhood.md` in the task records.
-/

set_option autoImplicit false

open Set Metric
open scoped ContDiff

namespace PoincareMT.M25.Topology3D

variable (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Smooth coordinates on a neighborhood of a closed ball, as retained
by Hatcher's ball pieces, Theorem 1.1 and Lemma 1.2, pp. 1-3. -/
structure BallNeighborhoodChart where
  chart : OpenPartialHomeomorph E F
  closedBall_subset_source : closedBall 0 1 ⊆ chart.source
  smooth : ContDiffOn ℝ ∞ chart chart.source
  smooth_symm : ContDiffOn ℝ ∞ chart.symm chart.target

namespace BallNeighborhoodChart

variable {E F} (B : BallNeighborhoodChart E F)

/-- The bounded open region represented by the ball coordinates. -/
def inside : Set F := B.chart '' ball 0 1

/-- The compact region represented by the closed ball coordinates. -/
def closedRegion : Set F := B.chart '' closedBall 0 1

/-- The sphere represented by the boundary coordinates. -/
def boundary : Set F := B.chart '' sphere 0 1

/-- The charted inside is open in the ambient space. -/
theorem inside_open : IsOpen B.inside :=
  B.chart.isOpen_image_of_subset_source isOpen_ball
    (ball_subset_closedBall.trans B.closedBall_subset_source)

/-- The charted inside is connected, including a zero-dimensional source. -/
theorem inside_connected : IsConnected B.inside := by
  exact (convex_ball (0 : E) (1 : ℝ)).isConnected (nonempty_ball.mpr zero_lt_one) |>.image
    B.chart (B.chart.continuousOn.mono
      (ball_subset_closedBall.trans B.closedBall_subset_source))

/-- Boundary and interior images remain disjoint by chart injectivity. -/
theorem inside_disjoint_boundary : Disjoint B.inside B.boundary := by
  apply Set.disjoint_left.mpr
  rintro y ⟨x, hx, rfl⟩ ⟨z, hz, heq⟩
  have hzx := B.chart.injOn
    (B.closedBall_subset_source (sphere_subset_closedBall hz))
    (B.closedBall_subset_source (ball_subset_closedBall hx)) heq
  subst z
  exact (ne_of_lt (mem_ball_zero_iff.mp hx)) (mem_sphere_zero_iff_norm.mp hz)

variable [ProperSpace E]

/-- The chart extends past the closed unit ball by a uniform radius. -/
theorem exists_larger_ball : ∃ R : ℝ, 1 < R ∧ ball 0 R ⊆ B.chart.source := by
  obtain ⟨d, hd, hsub⟩ := (isCompact_closedBall (0 : E) 1).exists_thickening_subset_open
    B.chart.open_source B.closedBall_subset_source
  rw [thickening_closedBall hd zero_le_one] at hsub
  exact ⟨d + 1, by linarith, hsub⟩

/-- The closed region is compact because the chart is continuous on it. -/
theorem closedRegion_compact : IsCompact B.closedRegion :=
  (isCompact_closedBall (0 : E) 1).image_of_continuousOn
    (B.chart.continuousOn.mono B.closedBall_subset_source)

/-- Compact containment proves boundedness of the charted inside. -/
theorem inside_bounded : Bornology.IsBounded B.inside :=
  B.closedRegion_compact.isBounded.subset (image_mono ball_subset_closedBall)

/-- The closed region is exactly the closure of the inside. -/
theorem closure_inside : closure B.inside = B.closedRegion :=
  compactChart_closure_ball B.chart 0 zero_lt_one B.closedBall_subset_source

/-- The charted sphere is exactly the frontier of the inside. -/
theorem frontier_inside : frontier B.inside = B.boundary :=
  compactChart_frontier_ball B.chart 0 zero_lt_one B.closedBall_subset_source

omit [ProperSpace E] in
/-- The inside and its boundary together make the closed region. -/
theorem inside_union_boundary : B.inside ∪ B.boundary = B.closedRegion := by
  change B.chart '' ball 0 1 ∪ B.chart '' sphere 0 1 = B.chart '' closedBall 0 1
  rw [← image_union, ball_union_sphere]

/-- In dimension greater than one, the outside of a charted closed ball
is connected; Hatcher's ball separation, Theorem 1.1, pp. 1-2. -/
theorem outside_connected (hdim : 1 < Module.rank ℝ E) :
    IsConnected (univ \ (B.inside ∪ B.boundary)) := by
  obtain ⟨R, hR, hsub⟩ := B.exists_larger_ball
  rw [B.inside_union_boundary, ← compl_eq_univ_sdiff]
  exact compactChart_exterior_connected B.chart hdim hR hsub

end BallNeighborhoodChart
end PoincareMT.M25.Topology3D
