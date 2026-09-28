import PoincareConjecture.Proofs.M01.NormalizationVolume









set_option autoImplicit false

open MeasureTheory Metric
open scoped ENNReal

namespace PoincareConjecture

theorem m01_euclideanHausdorff_unitBall_lt_top :
    euclideanUnitBallHausdorffVolume < ⊤ := by
  let := m01_euclideanHausdorff_locallyFinite
  exact Metric.isBounded_ball.measure_lt_top

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F]

theorem m01_hausdorff_ball_of_linearIsometryEquiv
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

theorem m01_calibrated_hausdorff_ball
    (e : F ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) (a : F) {r : ℝ} (hr : 0 < r) :
    euclideanHausdorffCalibration * Measure.hausdorffMeasure (3 : ℝ) (Metric.ball a r) =
      euclideanUnitBallLebesgueVolume * ENNReal.ofReal r ^ 3 := by
  rw [m01_hausdorff_ball_of_linearIsometryEquiv e a hr]
  calc
    euclideanHausdorffCalibration *
        (ENNReal.ofReal r ^ 3 * euclideanUnitBallHausdorffVolume) =
        (euclideanUnitBallLebesgueVolume / euclideanUnitBallHausdorffVolume *
          euclideanUnitBallHausdorffVolume) * ENNReal.ofReal r ^ 3 := by
      unfold euclideanHausdorffCalibration
      ac_rfl
    _ = euclideanUnitBallLebesgueVolume * ENNReal.ofReal r ^ 3 := by
      rw [ENNReal.div_mul_cancel m01_euclideanHausdorff_unitBall_pos.ne'
        m01_euclideanHausdorff_unitBall_lt_top.ne]

end PoincareConjecture
