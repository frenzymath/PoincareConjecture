import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Harnack.Matrix.Bounds
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.TensorPullback
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients.ChristoffelEstimate











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.LeviCivitaData

open ConnectionVariation CoordinateExponential

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}


theorem fderiv_ricci_eq_covariant_add_christoffel (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x d u v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun y => D.ricci y u v) x d =
      D.covariantTensorDerivative D.ricciEvaluation x ![d, u, v] +
        D.ricci x (christoffelBilinear g.euclideanCoefficients x d u) v +
        D.ricci x u (christoffelBilinear g.euclideanCoefficients x d v) := by
  have h := D.fderiv_covariantTensor_pullback_model hD.2.1
    (q := id) (V := fun i _ => (![u, v] : Fin 2 → EuclideanSpace ℝ (Fin n)) i)
    (p := x) differentiableAt_id (fun _ => differentiableAt_const _) d
  simpa [manifoldCovDerivAlong_model, covDerivAlong_def, ricciEvaluation,
    Fin.sum_univ_two, Function.update, add_assoc] using h



theorem norm_fderiv_ricci_le (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x u v : EuclideanSpace ℝ (Fin n)) {c G K L : ℝ}
    (hc : 0 ≤ c) (hG : 0 ≤ G) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hnorm : ∀ w, g.tangentNorm x w ≤ c * ‖w‖)
    (hΓ : ‖christoffelBilinear g.euclideanCoefficients x‖ ≤ G)
    (hcurv : D.curvatureDerivativeNorm 0 x ≤ K)
    (hcurv' : D.curvatureDerivativeNorm 1 x ≤ L) :
    ‖fderiv ℝ (fun y => D.ricci y u v) x‖ ≤
      ((n : ℝ) * L * c ^ 3 + 2 * (n : ℝ) * K * c ^ 2 * G) * ‖u‖ * ‖v‖ := by
  have hN (w : EuclideanSpace ℝ (Fin n)) : 0 ≤ g.tangentNorm x w := Real.sqrt_nonneg _
  have hN₀ : 0 ≤ D.curvatureDerivativeNorm 0 x := Real.sqrt_nonneg _
  have hN₁ : 0 ≤ D.curvatureDerivativeNorm 1 x := Real.sqrt_nonneg _
  have hC (d w : EuclideanSpace ℝ (Fin n)) :
      g.tangentNorm x (christoffelBilinear g.euclideanCoefficients x d w) ≤
        c * G * ‖d‖ * ‖w‖ := by
    calc
      _ ≤ c * ‖christoffelBilinear g.euclideanCoefficients x d w‖ := hnorm _
      _ ≤ c * (G * ‖d‖ * ‖w‖) := by
        apply mul_le_mul_of_nonneg_left _ hc
        exact ((christoffelBilinear g.euclideanCoefficients x).le_opNorm₂ d w).trans
          (by gcongr)
      _ = _ := by ring
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro d
  rw [Real.norm_eq_abs, D.fderiv_ricci_eq_covariant_add_christoffel hD]
  have h₁ : |D.covariantTensorDerivative D.ricciEvaluation x ![d, u, v]| ≤
      (n : ℝ) * L * (c * ‖d‖) * (c * ‖u‖) * (c * ‖v‖) := by
    refine (D.abs_covariantTensorDerivative_ricci_le_curvatureDerivativeNorm hD x d u v).trans ?_
    gcongr <;> first | exact hN _ | exact hnorm _
  have h₂ : |D.ricci x (christoffelBilinear g.euclideanCoefficients x d u) v| ≤
      (n : ℝ) * K * (c * G * ‖d‖ * ‖u‖) * (c * ‖v‖) := by
    refine (D.abs_ricci_le_curvatureDerivativeNorm_zero hD x _ v).trans ?_
    gcongr <;> first | exact hN _ | exact hC d u | exact hnorm v
  have h₃ : |D.ricci x u (christoffelBilinear g.euclideanCoefficients x d v)| ≤
      (n : ℝ) * K * (c * ‖u‖) * (c * G * ‖d‖ * ‖v‖) := by
    refine (D.abs_ricci_le_curvatureDerivativeNorm_zero hD x u _).trans ?_
    gcongr <;> first | exact hN _ | exact hnorm u | exact hC d v
  have htri := (abs_add_le
    (D.covariantTensorDerivative D.ricciEvaluation x ![d, u, v] +
      D.ricci x (christoffelBilinear g.euclideanCoefficients x d u) v)
    (D.ricci x u (christoffelBilinear g.euclideanCoefficients x d v))).trans
    (add_le_add (abs_add_le _ _) le_rfl)
  nlinarith only [htri, h₁, h₂, h₃]

end PoincareConjecture.LeviCivitaData
