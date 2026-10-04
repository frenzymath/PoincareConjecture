import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.ContinuousOn

/-!
# Compact convex coordinate neighborhoods

The local box used in Morgan-Tian Corollary 6.79, pp. 144-145.
A continuous coordinate map on an open source has a smaller open
source whose image lies in one compact convex subset of a prescribed
open coordinate region. No positive dimension is required.
-/

set_option autoImplicit false

open Set
open scoped Topology

namespace PoincareMT.M14

variable {X E : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- Restrict a continuous coordinate map to an open neighborhood with
compact convex image control, the box choice for Corollary 6.79,
pp. 144-145. -/
theorem exists_compact_convex_coordinate_box {U : Set X} (hU : IsOpen U)
    {x : X} (hx : x ∈ U) (f : X → E) (hf : ContinuousOn f U)
    {V : Set E} (hV : IsOpen V) (hfx : f x ∈ V) :
    ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ O ⊆ U ∧
      ∃ S : Set E, IsCompact S ∧ Convex ℝ S ∧ S ⊆ V ∧ MapsTo f O S := by
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hfx)
  refine ⟨U ∩ f ⁻¹' Metric.ball (f x) r,
    hf.isOpen_inter_preimage hU Metric.isOpen_ball,
    ⟨hx, Metric.mem_ball_self hr⟩, inter_subset_left,
    Metric.closedBall (f x) r, isCompact_closedBall _ _, convex_closedBall _ _, hball, ?_⟩
  exact fun _ hy => Metric.ball_subset_closedBall hy.2

end PoincareMT.M14
