import PoincareConjecture.Proofs.M34.Standard.CoordinateConnector
import PoincareConjecture.Proofs.M09.SquareActionComparison

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff intervalIntegral

universe u

namespace PoincareConjecture.M34

open Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem squareCurveActionDensity_le_of_tangentNorm_le {J : Set ℝ}
    (F : RicciFlow n M J) (T : ℝ) (beta : ℝ → M) (s : ℝ) {L R v : ℝ}
    (hR : 0 ≤ R) (hs : s ^ 2 ≤ L)
    (hscalar : (F.connection (T - s ^ 2)).scalarCurvature (beta s) ≤ R)
    (hspeed : (F.metric (T - s ^ 2)).tangentNorm (beta s)
      (curveVelocity beta s) ≤ v) :
    squareCurveActionDensity F T beta s ≤ 2 * L * R + v ^ 2 / 2 := by
  let g := F.metric (T - s ^ 2)
  let w := curveVelocity (n := n) beta s
  have hnonneg : 0 ≤ g.inner (beta s) w w := by
    by_cases hw : w = 0
    · simp [hw]
    · exact (g.pos (beta s) w hw).le
  have henergy : regularizedCurveEnergy F T beta s ≤ v ^ 2 := by
    change g.inner (beta s) w w ≤ v ^ 2
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg (g.inner (beta s) w w)) hspeed 2
    simpa only [RiemannianMetric.tangentNorm, Real.sq_sqrt hnonneg] using h
  have hcurv : 2 * s ^ 2 * (F.connection (T - s ^ 2)).scalarCurvature (beta s) ≤
      2 * L * R := calc
    _ ≤ 2 * s ^ 2 * R := mul_le_mul_of_nonneg_left hscalar (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hR
  dsimp only [squareCurveActionDensity]
  linarith

theorem coordinateConnector_squareActionDensity_le {J : Set ℝ}
    (F : RicciFlow n M J) (T : ℝ) (f : E → M)
    {a b delta c C L R : ℝ} (hab : a < b) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (htransition : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C) {z : E}
    (hz : z ∈ Metric.ball 0 delta)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f (Metric.ball 0 delta))
    (s : ℝ) (hR : 0 ≤ R) (hs : s ^ 2 ≤ L)
    (hscalar : ∀ x : M, (F.connection (T - s ^ 2)).scalarCurvature x ≤ R)
    (hbound : ∀ x ∈ Metric.ball 0 delta, ∀ v : E,
      (F.metric (T - s ^ 2)).tangentNorm (f x)
        (mfderiv (𝓡 n) (𝓡 n) f x v) ≤ c * ‖v‖) :
    squareCurveActionDensity F T (coordinateConnector f a b z) s ≤
      2 * L * R + (c * (C / (b - a)) * delta) ^ 2 / 2 :=
  squareCurveActionDensity_le_of_tangentNorm_le F T _ s hR hs (hscalar _)
    (coordinateConnector_tangentNorm_le _ f hab hc hC htransition hz hf hbound s)

theorem squareCurveActionIntegral_le {J : Set ℝ} (F : RicciFlow n M J)
    (P : RicciFlowCurvatureTheory.{u}) (T taumax : ℝ) (hmax : 0 < taumax)
    (hwindow : Icc (T - taumax) T ⊆ J) {tau a B : ℝ}
    (htau : 0 < tau) (htaumax : tau < taumax) (ha : 0 ≤ a)
    (hat : a ≤ Real.sqrt tau) (beta : ℝ → M)
    (hbeta : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) ∞ beta)
    (hbound : ∀ s ∈ Icc a (Real.sqrt tau), squareCurveActionDensity F T beta s ≤ B) :
    (∫ s in a..Real.sqrt tau, squareCurveActionDensity F T beta s) ≤
      B * (Real.sqrt tau - a) := by
  have hi := squareCurveActionDensity_intervalIntegrable F P T taumax hmax hwindow
    tau htau htaumax beta univ isOpen_univ (subset_univ _) hbeta.contMDiffOn
  have hi' : IntervalIntegrable (squareCurveActionDensity F T beta) volume
      a (Real.sqrt tau) := hi.mono_set (by
    rw [uIcc_of_le hat, uIcc_of_le (Real.sqrt_nonneg tau)]
    exact Icc_subset_Icc ha le_rfl)
  have h := intervalIntegral.integral_mono_on hat hi'
    (intervalIntegrable_const (c := B)) hbound
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h

end PoincareConjecture.M34
