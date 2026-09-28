import PoincareConjecture.Proofs.M47.BlowupControlsCapOperatorNorm
import PoincareConjecture.Proofs.M47.BlowupControlsCapThreeArrays
import PoincareConjecture.Proofs.M47.BlowupControlsCapInverseCoefficients
import PoincareConjecture.Proofs.M47.BlowupControlsCapMetricSymmetry










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M47

local notation "I" => Fin 3
local notation "V" => EuclideanSpace ℝ I

theorem cap_inverseCoefficient_fderiv_eq_components
    (g : RiemannianMetric 3 V) (e : V ≃L[ℝ] V) (x u : V) (i j : I) :
    fderiv ℝ (fun y => M04.frameInverseGram g y e.toContinuousLinearMap i j) x u =
      capOperatorComponents (fderiv ℝ
        (fun y => (M04.frameGramOperator g y e.toContinuousLinearMap).inverse) x u) (i, j) := by
  rw [cap_frameInverseGram_fderiv g e x u i j]
  rw [cap_inverse_fderiv_apply _
    ((cap_frameGram_contDiff g e.toContinuousLinearMap).differentiable (by simp) x)
    (M04.frameGramOperator_isInvertible g x e) u]
  rfl

theorem cap_gramDerivative_components_normal
    {g0 g1 : RiemannianMetric 3 V} (D0 : LeviCivitaData g0)
    (e : V ≃L[ℝ] V) (x : V)
    (hzero : ∀ u v : V, D0.euclideanConnection u v x = 0) (i j k : I) :
    let b := EuclideanSpace.basisFun I ℝ
    let H : CovariantTensorEvaluation 3 V 2 :=
      fun y z => g1.inner y (z 0) (z 1) - g0.inner y (z 0) (z 1)
    capOperatorComponents (fderiv ℝ
      (fun y => M04.frameGramOperator g1 y e.toContinuousLinearMap) x (e (b i))) (j, k) =
      D0.covariantTensorDerivative H x ![e (b i), e (b j), e (b k)] := by
  let b := EuclideanSpace.basisFun I ℝ
  change inner ℝ (b j) ((fderiv ℝ
    (fun y => M04.frameGramOperator g1 y e.toContinuousLinearMap) x (e (b i))) (b k)) = _
  rw [real_inner_comm, cap_frameGram_fderiv_normal D0 e x hzero]
  exact cap_metricDifference_derivative_symm D0 x (e (b i)) (e (b k)) (e (b j))



theorem cap_inverseDerivative_tensor_norm_le
    {g0 g1 : RiemannianMetric 3 V} (D0 : LeviCivitaData g0)
    (e : V ≃L[ℝ] V) (x : V)
    (hzero : ∀ u v : V, D0.euclideanConnection u v x = 0)
    {a : ℝ} (ha : 0 ≤ a)
    (hA : ‖(M04.frameGramOperator g1 x e.toContinuousLinearMap).inverse‖ ≤ a) :
    let b := EuclideanSpace.basisFun I ℝ
    let H : CovariantTensorEvaluation 3 V 2 :=
      fun y z => g1.inner y (z 0) (z 1) - g0.inner y (z 0) (z 1)
    let P := fun i j k => D0.covariantTensorDerivative H x ![e (b i), e (b j), e (b k)]
    let U := fun i j k => fderiv ℝ
      (fun y => M04.frameInverseGram g1 y e.toContinuousLinearMap j k) x (e (b i))
    ‖capThreeTensorComponents U‖ ≤ a ^ 2 * ‖capThreeTensorComponents P‖ := by
  let b := EuclideanSpace.basisFun I ℝ
  let H : CovariantTensorEvaluation 3 V 2 :=
    fun y z => g1.inner y (z 0) (z 1) - g0.inner y (z 0) (z 1)
  let P := fun i j k => D0.covariantTensorDerivative H x ![e (b i), e (b j), e (b k)]
  let U := fun i j k => fderiv ℝ
    (fun y => M04.frameInverseGram g1 y e.toContinuousLinearMap j k) x (e (b i))
  let G := fun y => M04.frameGramOperator g1 y e.toContinuousLinearMap
  have hG : DifferentiableAt ℝ G x :=
    (cap_frameGram_contDiff g1 e.toContinuousLinearMap).differentiable (by simp) x
  have hi : (G x).IsInvertible := M04.frameGramOperator_isInvertible g1 x e
  have hA2 : ‖(G x).inverse‖ ^ 2 ≤ a ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) ha).mpr hA
  have hUeq (i j k : I) : U i j k = capOperatorComponents
      (fderiv ℝ (fun y => (G y).inverse) x (e (b i))) (j, k) :=
    cap_inverseCoefficient_fderiv_eq_components g1 e x (e (b i)) j k
  have hPeq (i j k : I) : capOperatorComponents
      (fderiv ℝ G x (e (b i))) (j, k) = P i j k :=
    cap_gramDerivative_components_normal D0 e x hzero i j k
  change ‖capThreeTensorComponents U‖ ≤ a ^ 2 * ‖capThreeTensorComponents P‖
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (sq_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, cap_threeTensor_norm_sq, cap_threeTensor_norm_sq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hbound := (cap_inverse_derivative_components_norm_le hG hi
    (v := e (b i))).trans (mul_le_mul_of_nonneg_right hA2 (norm_nonneg _))
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (sq_nonneg _) (norm_nonneg _))).mpr hbound
  have hUnorm : ‖capOperatorComponents
      (fderiv ℝ (fun y => (G y).inverse) x (e (b i)))‖ ^ 2 =
      ∑ j, ∑ k, U i j k ^ 2 := by
    simpa only [Fintype.sum_prod_type, hUeq] using
      cap_array_norm_sq (capOperatorComponents
        (fderiv ℝ (fun y => (G y).inverse) x (e (b i))))
  have hPnorm : ‖capOperatorComponents (fderiv ℝ G x (e (b i)))‖ ^ 2 =
      ∑ j, ∑ k, P i j k ^ 2 := by
    simpa only [Fintype.sum_prod_type, hPeq] using
      cap_array_norm_sq (capOperatorComponents (fderiv ℝ G x (e (b i))))
  rwa [mul_pow, hUnorm, hPnorm] at hs

end PoincareConjecture.M47
