import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Standard.Radial.RadialDistance
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Standard.Radial.RadialInverse
import Mathlib.Analysis.Normed.Module.RCLike.Real

set_option autoImplicit false

open scoped ENNReal Topology

namespace PoincareConjecture.MetricSurgery

theorem standard_ball_eq_euclidean (g₀ : StandardInitialMetric) {r : ℝ} (hr : 0 < r) :
    g₀.metric.ball 0 r = Metric.ball 0 (radialEuclideanRadius g₀ r) := by
  ext x
  change g₀.metric.edist 0 x < ENNReal.ofReal r ↔ dist x 0 < radialEuclideanRadius g₀ r
  rw [standard_edist_zero, ENNReal.ofReal_lt_ofReal_iff hr, dist_zero_right]
  simpa only [radialArclength_euclideanRadius] using
    (radialArclength_strictMono g₀).lt_iff_lt (a := ‖x‖) (b := radialEuclideanRadius g₀ r)

theorem standard_closed_ball_eq_euclidean (g₀ : StandardInitialMetric)
    {r : ℝ} (hr : 0 ≤ r) :
    {x | g₀.metric.edist 0 x ≤ ENNReal.ofReal r} =
      Metric.closedBall 0 (radialEuclideanRadius g₀ r) := by
  ext x
  change g₀.metric.edist 0 x ≤ ENNReal.ofReal r ↔ dist x 0 ≤ radialEuclideanRadius g₀ r
  rw [standard_edist_zero, ENNReal.ofReal_le_ofReal_iff hr, dist_zero_right]
  simpa only [radialArclength_euclideanRadius] using
    (radialArclength_strictMono g₀).le_iff_le (a := ‖x‖) (b := radialEuclideanRadius g₀ r)

theorem standard_closed_ball_compact (g₀ : StandardInitialMetric)
    {r : ℝ} (hr : 0 ≤ r) :
    IsCompact {x | g₀.metric.edist 0 x ≤ ENNReal.ofReal r} := by
  rw [standard_closed_ball_eq_euclidean g₀ hr]
  exact isCompact_closedBall 0 _

theorem standard_closure_ball (g₀ : StandardInitialMetric) {r : ℝ} (hr : 0 < r) :
    closure (g₀.metric.ball 0 r) = {x | g₀.metric.edist 0 x ≤ ENNReal.ofReal r} := by
  rw [standard_ball_eq_euclidean g₀ hr, standard_closed_ball_eq_euclidean g₀ hr.le]
  exact closure_ball 0 ((radialEuclideanRadius_pos_iff g₀ r).mpr hr).ne'

theorem standard_frontier_ball (g₀ : StandardInitialMetric) {r : ℝ} (hr : 0 < r) :
    frontier (g₀.metric.ball 0 r) = {x | g₀.metric.edist 0 x = ENNReal.ofReal r} := by
  rw [standard_ball_eq_euclidean g₀ hr,
    frontier_ball 0 ((radialEuclideanRadius_pos_iff g₀ r).mpr hr).ne']
  ext x
  change dist x 0 = radialEuclideanRadius g₀ r ↔
    g₀.metric.edist 0 x = ENNReal.ofReal r
  have hnonneg : 0 ≤ radialArclength g₀ ‖x‖ := by
    simpa only [radialArclength_zero] using
      (radialArclength_strictMono g₀).monotone (norm_nonneg x)
  rw [dist_zero_right, standard_edist_zero, ENNReal.ofReal_eq_ofReal_iff hnonneg hr.le]
  constructor
  · intro hx
    rw [hx, radialArclength_euclideanRadius]
  · intro hx
    apply (radialArclength_strictMono g₀).injective
    exact hx.trans (radialArclength_euclideanRadius g₀ r).symm

end PoincareConjecture.MetricSurgery
