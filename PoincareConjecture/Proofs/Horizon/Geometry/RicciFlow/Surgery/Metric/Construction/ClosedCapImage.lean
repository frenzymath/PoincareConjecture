import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Standard.Radial.StandardBalls








set_option autoImplicit false

open scoped ENNReal Topology

namespace PoincareConjecture.MetricSurgery

theorem standard_closed_ball_image {N : Type*} [TopologicalSpace N] [T2Space N]
    (g₀ : StandardInitialMetric) {f : StandardCapSpace → N} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hf : ContinuousOn f (g₀.metric.ball 0 R)) :
    f '' {x | g₀.metric.edist 0 x ≤ ENNReal.ofReal r} =
      closure (f '' g₀.metric.ball 0 r) := by
  have hsubset : {x | g₀.metric.edist 0 x ≤ ENNReal.ofReal r} ⊆
      g₀.metric.ball 0 R := by
    intro x hx
    exact lt_of_le_of_lt hx (ENNReal.ofReal_lt_ofReal_iff (hr.trans hrR) |>.mpr hrR)
  have hc : IsCompact (closure (g₀.metric.ball 0 r)) := by
    rw [standard_closure_ball g₀ hr]
    exact standard_closed_ball_compact g₀ hr.le
  have hf' : ContinuousOn f (closure (g₀.metric.ball 0 r)) := by
    rw [standard_closure_ball g₀ hr]
    exact hf.mono hsubset
  simpa only [standard_closure_ball g₀ hr] using image_closure_of_isCompact hc hf'

theorem surgery_closed_cap_image {N : Type*} [TopologicalSpace N] [T2Space N]
    (g₀ : StandardInitialMetric) {f : StandardCapSpace → N}
    (hf : ContinuousOn f (g₀.metric.ball 0 (g₀.cylindrical_end.radius + 5))) :
    f '' {x | g₀.metric.edist 0 x ≤ ENNReal.ofReal (g₀.cylindrical_end.radius + 4)} =
      closure (f '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4)) := by
  apply standard_closed_ball_image g₀ (by linarith [g₀.cylindrical_end.radius_pos])
    (by linarith) hf

end PoincareConjecture.MetricSurgery
