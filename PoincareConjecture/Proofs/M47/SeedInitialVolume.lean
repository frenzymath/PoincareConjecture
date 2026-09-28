import PoincareConjecture.Definitions.Ch15.SurgeryFlow

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace PoincareConjecture.Proofs.M47

theorem initial_seed_density_pos : 0 < euclideanUnitBallLebesgueVolume.toReal / 2 := by
  apply div_pos ?_ (by norm_num)
  apply ENNReal.toReal_pos
  · exact ne_of_gt (Metric.measure_ball_pos volume
      (0 : EuclideanSpace ℝ (Fin 3)) (by norm_num : (0 : ℝ) < 1))
  · exact Metric.isBounded_ball.measure_lt_top.ne

theorem seed_initial_ball_volume (F : SurgeryFlowData) (q : (F.slice 0).carrier)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ENNReal.ofReal ((euclideanUnitBallLebesgueVolume.toReal / 2) * r ^ 3) ≤
      calibratedMetricVolume (F.metric 0) ((F.metric 0).ball q r) := by
  convert (F.initial_normalized q).2 r hr hr1 using 1
  congr 1
  ring

end PoincareConjecture.Proofs.M47
