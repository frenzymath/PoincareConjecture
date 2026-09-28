import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.OpenPartialHomeomorph.Basic

set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M25.Topology3D

section Topological

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]

theorem compactChart_closure_image (e : OpenPartialHomeomorph X Y) {s : Set X}
    (hc : IsCompact (closure s)) (hs : closure s ⊆ e.source) :
    closure (e '' s) = e '' closure s := by
  have he : ContinuousOn e (closure s) := e.continuousOn.mono hs
  exact subset_antisymm
    (closure_minimal (image_mono subset_closure) (hc.image_of_continuousOn he).isClosed)
    he.image_closure

theorem compactChart_frontier_image (e : OpenPartialHomeomorph X Y) {s : Set X}
    (ho : IsOpen s) (hc : IsCompact (closure s)) (hs : closure s ⊆ e.source) :
    frontier (e '' s) = e '' frontier s := by
  have he : IsOpen (e '' s) :=
    e.isOpen_image_of_subset_source ho (subset_closure.trans hs)
  calc
    frontier (e '' s) = closure (e '' s) \ e '' s := by
      rw [frontier, he.interior_eq]
    _ = e '' (closure s \ s) := by
      rw [compactChart_closure_image e hc hs,
        (e.injOn.mono hs).image_sdiff_subset subset_closure]
    _ = e '' frontier s := by rw [frontier, ho.interior_eq]

end Topological

section Ball

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
variable [TopologicalSpace Y] [T2Space Y]

theorem compactChart_closure_ball (e : OpenPartialHomeomorph E Y) (x : E)
    {r : ℝ} (hr : 0 < r) (hs : closedBall x r ⊆ e.source) :
    closure (e '' ball x r) = e '' closedBall x r := by
  have hc : IsCompact (closure (ball x r)) := by
    rw [closure_ball x hr.ne']
    exact isCompact_closedBall x r
  have hsource : closure (ball x r) ⊆ e.source := by
    simpa only [closure_ball x hr.ne'] using hs
  rw [compactChart_closure_image e hc hsource, closure_ball x hr.ne']

theorem compactChart_frontier_ball (e : OpenPartialHomeomorph E Y) (x : E)
    {r : ℝ} (hr : 0 < r) (hs : closedBall x r ⊆ e.source) :
    frontier (e '' ball x r) = e '' sphere x r := by
  have hc : IsCompact (closure (ball x r)) := by
    rw [closure_ball x hr.ne']
    exact isCompact_closedBall x r
  have hsource : closure (ball x r) ⊆ e.source := by
    simpa only [closure_ball x hr.ne'] using hs
  rw [compactChart_frontier_image e isOpen_ball hc hsource, frontier_ball x hr.ne']

end Ball

end PoincareConjecture.M25.Topology3D
