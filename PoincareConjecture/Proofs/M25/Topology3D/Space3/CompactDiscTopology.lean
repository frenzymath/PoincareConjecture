import PoincareConjecture.Proofs.M25.Topology3D.Space3.CompactChart
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M25.Topology3D

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
variable [TopologicalSpace Y] [T2Space Y]

omit [ProperSpace E] [T2Space Y] in

theorem compactChart_interior_closedBall (e : OpenPartialHomeomorph E Y) (x : E)
    {r : ℝ} (hr : 0 < r) (hs : closedBall x r ⊆ e.source) :
    interior (e '' closedBall x r) = e '' ball x r := by
  have hi : e.IsImage (closedBall x r) (e '' closedBall x r) := by
    intro z hz
    constructor
    · rintro ⟨w, hw, hwz⟩
      have heq := e.injOn (hs hw) hz hwz
      simpa only [heq] using hw
    · intro hz'
      exact ⟨z, hz', rfl⟩
  have ht : e '' closedBall x r ⊆ e.target := by
    rintro y ⟨z, hz, rfl⟩
    exact e.map_source (hs hz)
  have h := hi.interior.image_eq
  rw [interior_closedBall x hr.ne',
    inter_eq_right.mpr (ball_subset_closedBall.trans hs),
    inter_eq_right.mpr (interior_subset.trans ht)] at h
  exact h.symm

theorem compactChart_frontier_closedBall (e : OpenPartialHomeomorph E Y) (x : E)
    {r : ℝ} (hr : 0 < r) (hs : closedBall x r ⊆ e.source) :
    frontier (e '' closedBall x r) = e '' sphere x r := by
  have hc : IsClosed (e '' closedBall x r) :=
    ((isCompact_closedBall x r).image_of_continuousOn (e.continuousOn.mono hs)).isClosed
  rw [frontier, hc.closure_eq, compactChart_interior_closedBall e x hr hs,
    ← (e.injOn.mono hs).image_sdiff_subset ball_subset_closedBall, closedBall_sdiff_ball]

end PoincareConjecture.M25.Topology3D
