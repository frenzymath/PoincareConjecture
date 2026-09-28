import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.RoundCurvature.CovariantCurvature

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.LeviCivitaData

open CoordinateExponential SingularRegularLimit.RoundComparison

variable {n : ℕ} {g h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

theorem metric_first_derivative_eq_covariantMetricDifference
    (Dg : LeviCivitaData g) (x a b c : EuclideanSpace ℝ (Fin n))
    (hzero : christoffelBilinear g.euclideanCoefficients x = 0) :
    fderiv ℝ (fun y => h.inner y b c) x a =
      Dg.covariantTensorDerivative (metricDifferenceTensor g h) x ![a, b, c] := by
  have hconn (a b : EuclideanSpace ℝ (Fin n)) : Dg.euclideanConnection a b x = 0 := by
    rw [euclideanConnection, Dg.connection_const_eq_inverse]
    change christoffelBilinear g.euclideanCoefficients x a b = 0
    simp only [hzero, zero_apply]
  have hgder : fderiv ℝ (fun y => g.inner y b c) x a = 0 := by
    have he := iteratedFDeriv_one_metric_inner g x a b c
    simp only [iteratedFDeriv_one_apply, Matrix.cons_val_zero] at he
    rw [he, Dg.metric_fderiv_eq_connection_pairings]
    simp only [hconn, map_zero, zero_apply, add_zero]
  have hsm (g' : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) :
      DifferentiableAt ℝ (fun y => g'.inner y b c) x :=
    (((g'.contDiffAt_euclideanCoefficients x).clm_apply contDiffAt_const).clm_apply
      contDiffAt_const).differentiableAt (by simp)
  erw [Dg.covariantTensorDerivative_eq_fderiv_of_christoffel_zero
    (metricDifferenceTensor_isSmooth g h) x a ![b, c] hzero]
  change _ = fderiv ℝ (fun y => h.inner y b c - g.inner y b c) x a
  rw [fderiv_fun_sub (hsm h) (hsm g)]
  simp only [sub_apply, hgder, sub_zero]

theorem abs_euclideanConnection_pairing_le_of_covariantMetricDifference
    (Dg : LeviCivitaData g) (Dh : LeviCivitaData h)
    (x : EuclideanSpace ℝ (Fin n)) {epsilon : ℝ}
    (hzero : christoffelBilinear g.euclideanCoefficients x = 0)
    (hfirst : ∀ a b c : EuclideanSpace ℝ (Fin n),
      |Dg.covariantTensorDerivative (metricDifferenceTensor g h) x ![a, b, c]| ≤
        epsilon * ‖a‖ * ‖b‖ * ‖c‖)
    (a b c : EuclideanSpace ℝ (Fin n)) :
    |h.inner x (Dh.euclideanConnection a b x) c| ≤
      (3 / 2 : ℝ) * epsilon * ‖a‖ * ‖b‖ * ‖c‖ := by
  have hp := Dh.inner_connection_const x a b c
  change 2 * h.inner x (Dh.euclideanConnection a b x) c = _ at hp
  rw [Dg.metric_first_derivative_eq_covariantMetricDifference x a b c hzero,
    Dg.metric_first_derivative_eq_covariantMetricDifference x b c a hzero,
    Dg.metric_first_derivative_eq_covariantMetricDifference x c a b hzero] at hp
  have h₁ := abs_le.mp (hfirst a b c)
  have h₂ := abs_le.mp (hfirst b c a)
  have h₃ := abs_le.mp (hfirst c a b)
  rw [abs_le]
  constructor <;> nlinarith

theorem norm_euclideanConnection_le_of_covariantMetricDifference
    (Dg : LeviCivitaData g) (Dh : LeviCivitaData h)
    (x : EuclideanSpace ℝ (Fin n)) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hepsilon_one : epsilon < 1)
    (hnormal : g.euclideanCoefficients x = innerSL ℝ)
    (hzero : christoffelBilinear g.euclideanCoefficients x = 0)
    (hmetric : ∀ w : EuclideanSpace ℝ (Fin n),
      |metricDifferenceTensor g h x ![w, w]| ≤ epsilon * ‖w‖ ^ 2)
    (hfirst : ∀ a b c : EuclideanSpace ℝ (Fin n),
      |Dg.covariantTensorDerivative (metricDifferenceTensor g h) x ![a, b, c]| ≤
        epsilon * ‖a‖ * ‖b‖ * ‖c‖)
    (a b : EuclideanSpace ℝ (Fin n)) :
    ‖Dh.euclideanConnection a b x‖ ≤
      (3 * epsilon / (2 * (1 - epsilon))) * ‖a‖ * ‖b‖ := by
  let A := Dh.euclideanConnection a b x
  have hmodel : g.inner x A A = ‖A‖ ^ 2 := by
    change g.euclideanCoefficients x A A = _
    rw [hnormal]
    exact real_inner_self_eq_norm_sq A
  have hlow := (abs_le.mp (hmetric A)).1
  change -(epsilon * ‖A‖ ^ 2) ≤ h.inner x A A - g.inner x A A at hlow
  rw [hmodel] at hlow
  have hupp := (le_abs_self (h.inner x A A)).trans
    (Dg.abs_euclideanConnection_pairing_le_of_covariantMetricDifference Dh x hzero
      hfirst a b A)
  change h.inner x A A ≤ (3 / 2 : ℝ) * epsilon * ‖a‖ * ‖b‖ * ‖A‖ at hupp
  have hden : 0 < 2 * (1 - epsilon) := by linarith
  by_cases hA : ‖A‖ = 0
  · change ‖A‖ ≤ _
    rw [hA]
    positivity
  · have hApos : 0 < ‖A‖ := lt_of_le_of_ne (norm_nonneg A) (Ne.symm hA)
    have hlin : 2 * (1 - epsilon) * ‖A‖ ≤ 3 * epsilon * ‖a‖ * ‖b‖ := by
      nlinarith
    change ‖A‖ ≤ _
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
    exact (le_div_iff₀ hden).mpr (by nlinarith)

end PoincareConjecture.LeviCivitaData
