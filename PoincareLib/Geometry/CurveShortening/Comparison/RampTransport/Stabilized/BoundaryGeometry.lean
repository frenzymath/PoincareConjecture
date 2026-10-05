import PoincareLib.Geometry.CurveShortening.Comparison.RampTransport.Stabilized.SmoothApproximation
import PoincareLib.Geometry.CurveShortening.Comparison.RampTransport.Constant.LiftDensities

/-!
# Geometry of the actual separated smooth boundaries

The constant auxiliary lifts retain immersion, length approximation and
the strict 3/400 turning margin at radius r/2 without a further error.
Source: MT2007 Lemma 19.31, pp. 464-466; ramp transport approximation
derivation, exact constant-lift scalar geometry.

Morgan--Tian context: the annulus in Lemma 19.31, printed pp. 464-466, and its intrinsic
comparison in Proposition 19.35, printed pp. 467-478.
-/

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped Manifold ContDiff

namespace PoincareMT.M64.RampTransport.StabilizedSmoothRampApproximation

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}
  {P : M62.CircleProductData F circumference}
  {Q : M62.CircleProductData P.flow auxiliary} {time : ℝ}
  {gamma0 gamma1 : ℝ → P.charts.Point}
  {A : M64Annulus (P.flow.metric time) gamma0 gamma1} {r epsilon : ℝ}

/-- The lower constant auxiliary lift is immersed.
Source: MT Lemma 19.31, pp. 464-466; stabilized approximation derivation. -/
theorem lower_immersed
    (S : StabilizedSmoothRampApproximation P Q time gamma0 gamma1 A r epsilon) :
    ∀ x, curveVelocity (n := (n + 1) + 1)
      (auxiliaryCircleSection Q (Q.circle.quotient 0) ∘ S.approximation.first) x ≠ 0 :=
  constantLift_immersed Q _ (S.approximation.first_smooth.of_le (by simp))
    (M63.ramp_immersed P S.approximation.first_ramp)

/-- The upper constant auxiliary lift is immersed.
Source: MT Lemma 19.31, pp. 464-466; stabilized approximation derivation. -/
theorem upper_immersed
    (S : StabilizedSmoothRampApproximation P Q time gamma0 gamma1 A r epsilon) :
    ∀ x, curveVelocity (n := (n + 1) + 1)
      (auxiliaryCircleSection Q (Q.circle.quotient S.separated.offset) ∘
        S.approximation.second) x ≠ 0 :=
  constantLift_immersed Q _ (S.approximation.second_smooth.of_le (by simp))
    (M63.ramp_immersed P S.approximation.second_ramp)

/-- Stabilization preserves the lower approximation's half-error budget.
Source: MT Lemma 19.31, pp. 464-466; stabilized approximation derivation. -/
theorem lower_length_error
    (S : StabilizedSmoothRampApproximation P Q time gamma0 gamma1 A r epsilon) :
    |m62Length Q.flow (fun y _ => auxiliaryCircleSection Q (Q.circle.quotient 0)
        (S.approximation.first y)) time -
      m62Length P.flow (fun y _ => gamma0 y) time| < epsilon / 2 := by
  rw [constantLift_length Q _ time (S.approximation.first_smooth.of_le (by simp))]
  exact S.approximation.first_length_error

/-- Stabilization preserves the upper approximation's half-error budget.
Source: MT Lemma 19.31, pp. 464-466; stabilized approximation derivation. -/
theorem upper_length_error
    (S : StabilizedSmoothRampApproximation P Q time gamma0 gamma1 A r epsilon) :
    |m62Length Q.flow (fun y _ => auxiliaryCircleSection Q
        (Q.circle.quotient S.separated.offset) (S.approximation.second y)) time -
      m62Length P.flow (fun y _ => gamma1 y) time| < epsilon / 2 := by
  rw [constantLift_length Q _ time (S.approximation.second_smooth.of_le (by simp))]
  exact S.approximation.second_length_error

/-- The stabilized lower boundary remains longer than half the original scale.
Source: MT Lemma 19.31, pp. 464-466; stabilized approximation derivation. -/
theorem lower_length_strict
    (S : StabilizedSmoothRampApproximation P Q time gamma0 gamma1 A r epsilon) :
    r / 2 < m62Length Q.flow (fun y _ => auxiliaryCircleSection Q (Q.circle.quotient 0)
      (S.approximation.first y)) time := by
  rw [constantLift_length Q _ time (S.approximation.first_smooth.of_le (by simp))]
  exact S.approximation.first_length_strict

/-- Stabilization retains the 3/400 turning margin on subarcs of length r/2.
Source: MT Lemma 19.31, pp. 464-466; stabilized approximation derivation. -/
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

end PoincareMT.M64.RampTransport.StabilizedSmoothRampApproximation
