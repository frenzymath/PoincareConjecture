import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.RoundCurvature.CovariantCoordinates
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.RoundCurvature.CoordinateBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComparison.ScalarModulus








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.LeviCivitaData

open CoordinateExponential SingularRegularLimit.RoundComparison

variable {n : ℕ} {g h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

theorem metricDifference_second_derivative
    (g h : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (x a b u v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => metricDifferenceTensor g h z ![u, v]) y b) x a =
      fderiv ℝ (fderiv ℝ h.euclideanCoefficients) x a b u v -
        fderiv ℝ (fderiv ℝ g.euclideanCoefficients) x a b u v := by
  have hsm (g' : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) :
      ContDiffAt ℝ ∞ (fun y => g'.inner y u v) x :=
    ((g'.contDiffAt_euclideanCoefficients x).clm_apply contDiffAt_const).clm_apply
      contDiffAt_const
  have hE : ContDiffAt ℝ ∞ (fun z => metricDifferenceTensor g h z ![u, v]) x :=
    (hsm h).sub (hsm g)
  have hs : fderiv ℝ (fun y => fderiv ℝ
      (fun z => metricDifferenceTensor g h z ![u, v]) y b) x a =
      iteratedFDeriv ℝ 2 (fun z => metricDifferenceTensor g h z ![u, v]) x ![a, b] := by
    rw [fderiv_clm_apply ((hE.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))
      (differentiableAt_const _)]
    simp [iteratedFDeriv_two_apply]
  rw [hs]
  have he := congrArg (fun L => L ![a, b])
    (fun_iteratedFDeriv_sub_apply
      ((hsm h).of_le (by norm_cast : (2 : ℕ∞ω) ≤ ∞))
      ((hsm g).of_le (by norm_cast : (2 : ℕ∞ω) ≤ ∞)))
  change iteratedFDeriv ℝ 2 (fun z => metricDifferenceTensor g h z ![u, v]) x ![a, b] =
    iteratedFDeriv ℝ 2 (fun z => h.inner z u v) x ![a, b] -
      iteratedFDeriv ℝ 2 (fun z => g.inner z u v) x ![a, b] at he
  rw [he, iteratedFDeriv_two_metric_inner, iteratedFDeriv_two_metric_inner]

theorem curvatureTensor_sub_eq_covariant_metricDifference
    (Dg : LeviCivitaData g) (Dh : LeviCivitaData h)
    (x u b v c : EuclideanSpace ℝ (Fin n))
    (hzero : christoffelBilinear g.euclideanCoefficients x = 0) :
    let H := metricDifferenceTensor g h
    let C := fun a b u v =>
      Dg.covariantTensorDerivative (Dg.covariantTensorDerivative H) x ![a, b, u, v]
    Dh.curvatureTensor x u b v c - Dg.curvatureTensor x u b v c =
      (2⁻¹ : ℝ) * (C u c b v - C u v b c - C b c u v + C b v u c) +
      (2⁻¹ : ℝ) * (H x ![Dg.curvature x u b c, v] - H x ![Dg.curvature x u b v, c]) +
      (h.inner x (Dh.euclideanConnection u c x) (Dh.euclideanConnection b v x) -
        h.inner x (Dh.euclideanConnection b c x) (Dh.euclideanConnection u v x)) := by
  have hconn (a b : EuclideanSpace ℝ (Fin n)) : Dg.euclideanConnection a b x = 0 := by
    rw [euclideanConnection, Dg.connection_const_eq_inverse]
    change christoffelBilinear g.euclideanCoefficients x a b = 0
    simp only [hzero, zero_apply]
  have hAlt := Dg.alternatingSecondDerivative_eq_covariant_add_curvature
    (metricDifferenceTensor_isSmooth g h) x u b v c hzero
  dsimp only at hAlt ⊢
  simp only [metricDifference_second_derivative] at hAlt
  rw [Dh.curvatureTensor_eq_second_deriv_add_connection_pairings,
    Dg.curvatureTensor_eq_second_deriv_add_connection_pairings]
  simp only [hconn, map_zero, sub_zero, add_zero]
  linarith

end PoincareConjecture.LeviCivitaData
