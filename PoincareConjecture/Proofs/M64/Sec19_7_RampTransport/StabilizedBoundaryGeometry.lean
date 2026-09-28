import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.StabilizedSmoothApproximation
import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.ConstantLiftDensities













set_option autoImplicit false
set_option warningAsError true

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M64.RampTransport.StabilizedSmoothRampApproximation

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}
  {P : M62.CircleProductData F circumference}
  {Q : M62.CircleProductData P.flow auxiliary} {time : ℝ}
  {gamma0 gamma1 : ℝ → P.charts.Point}
  {A : M64Annulus (P.flow.metric time) gamma0 gamma1} {r epsilon : ℝ}



theorem lower_immersed
    (S : StabilizedSmoothRampApproximation P Q time gamma0 gamma1 A r epsilon) :
    ∀ x, curveVelocity (n := (n + 1) + 1)
      (auxiliaryCircleSection Q (Q.circle.quotient 0) ∘ S.approximation.first) x ≠ 0 :=
  constantLift_immersed Q _ (S.approximation.first_smooth.of_le (by simp))
    (M63.ramp_immersed P S.approximation.first_ramp)



theorem upper_immersed
    (S : StabilizedSmoothRampApproximation P Q time gamma0 gamma1 A r epsilon) :
    ∀ x, curveVelocity (n := (n + 1) + 1)
      (auxiliaryCircleSection Q (Q.circle.quotient S.separated.offset) ∘
        S.approximation.second) x ≠ 0 :=
  constantLift_immersed Q _ (S.approximation.second_smooth.of_le (by simp))
    (M63.ramp_immersed P S.approximation.second_ramp)



theorem lower_length_error
    (S : StabilizedSmoothRampApproximation P Q time gamma0 gamma1 A r epsilon) :
    |m62Length Q.flow (fun y _ => auxiliaryCircleSection Q (Q.circle.quotient 0)
        (S.approximation.first y)) time -
      m62Length P.flow (fun y _ => gamma0 y) time| < epsilon / 2 := by
  rw [constantLift_length Q _ time (S.approximation.first_smooth.of_le (by simp))]
  exact S.approximation.first_length_error



theorem upper_length_error
    (S : StabilizedSmoothRampApproximation P Q time gamma0 gamma1 A r epsilon) :
    |m62Length Q.flow (fun y _ => auxiliaryCircleSection Q
        (Q.circle.quotient S.separated.offset) (S.approximation.second y)) time -
      m62Length P.flow (fun y _ => gamma1 y) time| < epsilon / 2 := by
  rw [constantLift_length Q _ time (S.approximation.second_smooth.of_le (by simp))]
  exact S.approximation.second_length_error



theorem lower_length_strict
    (S : StabilizedSmoothRampApproximation P Q time gamma0 gamma1 A r epsilon) :
    r / 2 < m62Length Q.flow (fun y _ => auxiliaryCircleSection Q (Q.circle.quotient 0)
      (S.approximation.first y)) time := by
  rw [constantLift_length Q _ time (S.approximation.first_smooth.of_le (by simp))]
  exact S.approximation.first_length_strict



theorem lower_turning
    (S : StabilizedSmoothRampApproximation P Q time gamma0 gamma1 A r epsilon)
    (alpha beta : ℝ) (hab : alpha ≤ beta) (hperiod : beta ≤ alpha + curvePeriod)
    (hlength : m63ArcLength Q.flow (fun y _ =>
      auxiliaryCircleSection Q (Q.circle.quotient 0) (S.approximation.first y))
        time alpha beta ≤ r / 2) :
    m63ArcTotalCurvature Q.flow (fun y _ =>
      auxiliaryCircleSection Q (Q.circle.quotient 0) (S.approximation.first y))
        time alpha beta < (3 / 400 : ℝ) := by
  rw [constantLift_arcLength Q _ time
    (S.approximation.first_smooth.of_le (by simp))] at hlength
  rw [constantLift_arcTotalCurvature Q _ time
    (S.approximation.first_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (M63.ramp_immersed P S.approximation.first_ramp)]
  exact S.approximation.first_turning alpha beta hab hperiod hlength

end PoincareConjecture.M64.RampTransport.StabilizedSmoothRampApproximation
