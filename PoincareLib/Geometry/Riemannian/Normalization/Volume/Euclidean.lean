import PoincareLib.Geometry.Riemannian.Normalization.Volume.Finite

/-!
# Euclidean calibration in an isometric model

The pointwise tangent metric is isometric to standard Euclidean three-space.
Hausdorff measure is invariant under that isometry, and the calibration
therefore gives the usual Euclidean volume at every center and positive radius.
-/

set_option autoImplicit false

open MeasureTheory Metric
open scoped ENNReal

namespace PoincareMT

theorem normalization_euclideanHausdorff_unitBall_lt_top :
    euclideanUnitBallHausdorffVolume < ⊤ := by
  let := normalization_euclideanHausdorff_locallyFinite
  exact Metric.isBounded_ball.measure_lt_top

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F]

theorem normalization_hausdorff_ball_of_linearIsometryEquiv
    (e : F ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) (a : F) {r : ℝ} (hr : 0 < r) :
    Measure.hausdorffMeasure (3 : ℝ) (Metric.ball a r) =
      ENNReal.ofReal r ^ 3 * euclideanUnitBallHausdorffVolume := by
  rw [← e.toIsometryEquiv.hausdorffMeasure_image (3 : ℝ) (Metric.ball a r),
    e.toIsometryEquiv.image_ball]
  have hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) : ℝ) = 3 := by simp
  rw [← hdim]
  rw [Measure.addHaar_ball_of_pos _ _ hr]
  have hdimNat : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  rw [hdimNat, ENNReal.ofReal_pow hr.le]
  rfl

theorem normalization_calibrated_hausdorff_ball
    (e : F ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) (a : F) {r : ℝ} (hr : 0 < r) :
    euclideanHausdorffCalibration * Measure.hausdorffMeasure (3 : ℝ) (Metric.ball a r) =
      euclideanUnitBallLebesgueVolume * ENNReal.ofReal r ^ 3 := by
  rw [normalization_hausdorff_ball_of_linearIsometryEquiv e a hr]
  calc
    euclideanHausdorffCalibration *
        (ENNReal.ofReal r ^ 3 * euclideanUnitBallHausdorffVolume) =
        (euclideanUnitBallLebesgueVolume / euclideanUnitBallHausdorffVolume *
          euclideanUnitBallHausdorffVolume) * ENNReal.ofReal r ^ 3 := by
      unfold euclideanHausdorffCalibration
      ac_rfl
    _ = euclideanUnitBallLebesgueVolume * ENNReal.ofReal r ^ 3 := by
      rw [ENNReal.div_mul_cancel normalization_euclideanHausdorff_unitBall_pos.ne'
        normalization_euclideanHausdorff_unitBall_lt_top.ne]

end PoincareMT
