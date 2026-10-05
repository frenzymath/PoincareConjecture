import PoincareLib.Geometry.RicciFlow.Surgery.Flow.Basic

/-!
# Uniform volume at the actual initial search endpoint

The raw normalized initial metric already supplies the required
cubic volume bound on every ball of radius at most one.
Source: MT Definition 4.10 and Uniform Seed, pp. 60 and 392-393.
-/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace PoincareMT.Proofs.M47

/-- The fixed normalized initial density is positive. -/
theorem initial_seed_density_pos : 0 < euclideanUnitBallLebesgueVolume.toReal / 2 := by
  apply div_pos ?_ (by norm_num)
  apply ENNReal.toReal_pos
  · exact ne_of_gt (Metric.measure_ball_pos volume
      (0 : EuclideanSpace ℝ (Fin 3)) (by norm_num : (0 : ℝ) < 1))
  · exact Metric.isBounded_ball.measure_lt_top.ne

/-- The literal initial metric supplies the seed volume; no rescaling
or comparison with a different initial metric occurs. -/
theorem seed_initial_ball_volume (F : SurgeryFlowData) (q : (F.slice 0).carrier)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ENNReal.ofReal ((euclideanUnitBallLebesgueVolume.toReal / 2) * r ^ 3) ≤
      calibratedMetricVolume (F.metric 0) ((F.metric 0).ball q r) := by
  convert (F.initial_normalized q).2 r hr hr1 using 1
  congr 1
  ring

end PoincareMT.Proofs.M47
