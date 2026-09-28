import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set

namespace UniformSpace.Completion

theorem radius_le_dist_of_precompact_ball
    {Y : Type*} [MetricSpace Y] (E : Completion Y)
    (houtside : E ∉ range ((↑) : Y → Completion Y))
    (x : Y) {rho : ℝ} (hcompact : IsCompact (closure (Metric.ball x rho))) :
    rho ≤ dist (x : Completion Y) E := by
  apply le_of_not_gt
  intro hsmall
  let K : Set (Completion Y) :=
    ((↑) : Y → Completion Y) '' closure (Metric.ball x rho)
  have hK : IsCompact K := hcompact.image (continuous_coe Y)
  have hEK : E ∈ K := by
    rw [← hK.isClosed.closure_eq]
    rw [Metric.mem_closure_iff]
    intro epsilon hepsilon
    obtain ⟨q, hq⟩ := denseRange_coe.exists_dist_lt E
      (lt_min hepsilon (sub_pos.mpr hsmall))
    have hqball : q ∈ Metric.ball x rho := by
      have htriangle := dist_triangle (x : Completion Y) E (q : Completion Y)
      rw [Completion.dist_eq] at htriangle
      have hclose := hq.trans_le (min_le_right _ _)
      rw [Metric.mem_ball, dist_comm]
      linarith only [htriangle, hclose]
    exact ⟨(q : Completion Y), ⟨q, subset_closure hqball, rfl⟩,
      hq.trans_le (min_le_left _ _)⟩
  obtain ⟨q, _hq, hqE⟩ := hEK
  exact houtside ⟨q, hqE⟩

end UniformSpace.Completion
