import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhood

set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M25.Topology3D

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace BallNeighborhoodChart

theorem interior_closedRegion (B : BallNeighborhoodChart E F) :
    interior B.closedRegion = B.inside := by
  apply Subset.antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := interior_subset hy
    have hxs := B.closedBall_subset_source hx
    have hpre : B.chart.source ∩ B.chart ⁻¹' interior B.closedRegion ⊆
        closedBall (0 : E) 1 := by
      rintro z ⟨hzs, hz⟩
      obtain ⟨w, hw, heq⟩ := interior_subset hz
      have hwz := B.chart.injOn (B.closedBall_subset_source hw) hzs heq
      exact hwz ▸ hw
    have hxi : x ∈ interior (closedBall (0 : E) 1) :=
      mem_interior_iff_mem_nhds.mpr
        (Filter.mem_of_superset
          ((B.chart.isOpen_inter_preimage isOpen_interior).mem_nhds ⟨hxs, hy⟩) hpre)
    rw [interior_closedBall (0 : E) one_ne_zero] at hxi
    exact ⟨x, hxi, rfl⟩
  · exact B.inside_open.subset_interior_iff.mpr (image_mono ball_subset_closedBall)

theorem closure_outside (B : BallNeighborhoodChart E F) :
    closure B.closedRegionᶜ = B.insideᶜ := by
  rw [closure_compl, B.interior_closedRegion]

theorem boundary_subset_closure_sides [ProperSpace E] (B : BallNeighborhoodChart E F) :
    B.boundary ⊆ closure B.inside ∩ closure B.closedRegionᶜ := by
  intro y hy
  rw [B.closure_inside, B.closure_outside]
  refine ⟨image_mono sphere_subset_closedBall hy, ?_⟩
  exact fun hin => Set.disjoint_left.mp B.inside_disjoint_boundary hin hy

end BallNeighborhoodChart
end PoincareConjecture.M25.Topology3D
