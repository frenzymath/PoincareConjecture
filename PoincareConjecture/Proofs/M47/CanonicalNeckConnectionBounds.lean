import PoincareConjecture.Proofs.M47.CanonicalNeckRicciCoefficients









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.Proofs.M47

open PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

private theorem abs_three_terms {a b c gamma : ℝ}
    (ha : |a| ≤ gamma) (hb : |b| ≤ gamma) (hc : |c| ≤ gamma) :
    |a + b - c| ≤ 3 * gamma := by
  calc
    _ ≤ |a + b| + |c| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (a + b) (-c)
    _ ≤ (|a| + |b|) + |c| := add_le_add (abs_add_le _ _) le_rfl
    _ ≤ _ := by linarith


theorem neck_connection_coefficient_bound {g0 g1 : RiemannianMetric 3 E}
    (D0 : LeviCivitaData g0) (D1 : LeviCivitaData g1) (x : E) (e : E ≃L[ℝ] E)
    (he : ∀ v w : E, g0.inner x (e v) (e w) = inner ℝ v w)
    {gamma : ℝ} (_hgamma : 0 ≤ gamma) (hsmall : gamma ≤ 1 / 2)
    (hbound0 : g0.tensorNorm (fun y (v : Fin 2 → TangentSpace (𝓡 3) y) =>
      g1.inner y (v 0) (v 1) - g0.inner y (v 0) (v 1)) x ≤ gamma)
    (hbound1 : g0.tensorNorm (D0.covariantTensorDerivative
      (fun y (v : Fin 2 → TangentSpace (𝓡 3) y) =>
        g1.inner y (v 0) (v 1) - g0.inner y (v 0) (v 1))) x ≤ gamma)
    (i j k : Fin 3) :
    |inner ℝ (EuclideanSpace.basisFun (Fin 3) ℝ i) (e.symm
      (D1.euclideanConnection (e (EuclideanSpace.basisFun (Fin 3) ℝ j))
          (e (EuclideanSpace.basisFun (Fin 3) ℝ k)) x -
        D0.euclideanConnection (e (EuclideanSpace.basisFun (Fin 3) ℝ j))
          (e (EuclideanSpace.basisFun (Fin 3) ℝ k)) x))| ≤ 9 * gamma := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  let H : CovariantTensorEvaluation 3 E 2 :=
    fun y v => g1.inner y (v 0) (v 1) - g0.inner y (v 0) (v 1)
  let H1 := D0.covariantTensorDerivative H
  have hH : IsSmoothCovariantTensor H := cap_metricDifference_smooth g0 g1
  have hH1 := M04.isSmoothCovariantTensor_covariantTensorDerivative D0 hH
  have hcomponent (a c d : Fin 3) : |H1 x ![e (b a), e (b c), e (b d)]| ≤ gamma :=
    neck_tensor_component_bound g0 x e he H1 hH1 hbound1 ![a, c, d]
  let S := fun l => H1 x ![e (b j), e (b k), e (b l)] +
    H1 x ![e (b k), e (b j), e (b l)] - H1 x ![e (b l), e (b j), e (b k)]
  have hS (l : Fin 3) : |S l| ≤ 3 * gamma :=
    abs_three_terms (hcomponent j k l) (hcomponent k j l) (hcomponent l j k)
  have hA := (neck_frame_inverse_bound x e he hsmall hbound0).2
  rw [cap_connectionDifference_coefficients D0 D1 e x]
  change |(1 / 2 : ℝ) * ∑ l, M04.frameInverseGram g1 x e.toContinuousLinearMap i l * S l| ≤ _
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc
    _ ≤ (1 / 2 : ℝ) * ∑ l : Fin 3,
        |M04.frameInverseGram g1 x e.toContinuousLinearMap i l * S l| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * ∑ _l : Fin 3, 2 * (3 * gamma) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro l _
      rw [abs_mul]
      exact mul_le_mul (hA i l) (hS l) (abs_nonneg _) (by norm_num)
    _ = _ := by simp; ring



theorem neck_connection_derivative_coefficient_bound {g0 g1 : RiemannianMetric 3 E}
    (D0 : LeviCivitaData g0) (D1 : LeviCivitaData g1) (x : E) (e : E ≃L[ℝ] E)
    (he : ∀ v w : E, g0.inner x (e v) (e w) = inner ℝ v w)
    (hzero : ∀ u v : E, D0.euclideanConnection u v x = 0)
    {gamma : ℝ} (hgamma : 0 ≤ gamma) (hsmall : gamma ≤ 1 / 2)
    (hbound0 : g0.tensorNorm (fun y (v : Fin 2 → TangentSpace (𝓡 3) y) =>
      g1.inner y (v 0) (v 1) - g0.inner y (v 0) (v 1)) x ≤ gamma)
    (hbound1 : g0.tensorNorm (D0.covariantTensorDerivative
      (fun y (v : Fin 2 → TangentSpace (𝓡 3) y) =>
        g1.inner y (v 0) (v 1) - g0.inner y (v 0) (v 1))) x ≤ gamma)
    (hbound2 : g0.tensorNorm (D0.covariantTensorDerivative (D0.covariantTensorDerivative
      (fun y (v : Fin 2 → TangentSpace (𝓡 3) y) =>
        g1.inner y (v 0) (v 1) - g0.inner y (v 0) (v 1)))) x ≤ gamma)
    (i j k l : Fin 3) :
    |inner ℝ (EuclideanSpace.basisFun (Fin 3) ℝ i) (e.symm
      (fderiv ℝ (fun y =>
        D1.euclideanConnection (e (EuclideanSpace.basisFun (Fin 3) ℝ j))
            (e (EuclideanSpace.basisFun (Fin 3) ℝ k)) y -
          D0.euclideanConnection (e (EuclideanSpace.basisFun (Fin 3) ℝ j))
            (e (EuclideanSpace.basisFun (Fin 3) ℝ k)) y) x
        (e (EuclideanSpace.basisFun (Fin 3) ℝ l))))| ≤ 9 * gamma + 162 * gamma ^ 2 := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  let H : CovariantTensorEvaluation 3 E 2 :=
    fun y v => g1.inner y (v 0) (v 1) - g0.inner y (v 0) (v 1)
  let H1 := D0.covariantTensorDerivative H
  let H2 := D0.covariantTensorDerivative H1
  have hH : IsSmoothCovariantTensor H := cap_metricDifference_smooth g0 g1
  have hH1 := M04.isSmoothCovariantTensor_covariantTensorDerivative D0 hH
  have hH2 := M04.isSmoothCovariantTensor_covariantTensorDerivative D0 hH1
  have hc1 (a c d : Fin 3) : |H1 x ![e (b a), e (b c), e (b d)]| ≤ gamma :=
    neck_tensor_component_bound g0 x e he H1 hH1 hbound1 ![a, c, d]
  have hc2 (a c d f : Fin 3) :
      |H2 x ![e (b a), e (b c), e (b d), e (b f)]| ≤ gamma :=
    neck_tensor_component_bound g0 x e he H2 hH2 hbound2 ![a, c, d, f]
  let S := fun m => H1 x ![e (b j), e (b k), e (b m)] +
    H1 x ![e (b k), e (b j), e (b m)] - H1 x ![e (b m), e (b j), e (b k)]
  let T := fun m => H2 x ![e (b l), e (b j), e (b k), e (b m)] +
    H2 x ![e (b l), e (b k), e (b j), e (b m)] -
      H2 x ![e (b l), e (b m), e (b j), e (b k)]
  have hS (m : Fin 3) : |S m| ≤ 3 * gamma :=
    abs_three_terms (hc1 j k m) (hc1 k j m) (hc1 m j k)
  have hT (m : Fin 3) : |T m| ≤ 3 * gamma :=
    abs_three_terms (hc2 l j k m) (hc2 l k j m) (hc2 l m j k)
  let A := fun m => M04.frameInverseGram g1 x e.toContinuousLinearMap i m
  let dA := fun m => fderiv ℝ
    (fun y => M04.frameInverseGram g1 y e.toContinuousLinearMap i m) x (e (b l))
  have hA (m : Fin 3) : |A m| ≤ 2 :=
    (neck_frame_inverse_bound x e he hsmall hbound0).2 i m
  have hdA (m : Fin 3) : |dA m| ≤ 36 * gamma :=
    neck_frame_inverse_derivative_bound D0 x e he hzero hgamma hsmall hbound0 hbound1 i m l
  rw [cap_connectionDifference_fderiv_normal D0 D1 e x hzero]
  change |(1 / 2 : ℝ) * ∑ m : Fin 3, (dA m * S m + A m * T m)| ≤ _
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc
    _ ≤ (1 / 2 : ℝ) * ∑ m : Fin 3, |dA m * S m + A m * T m| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * ∑ _m : Fin 3, (36 * gamma * (3 * gamma) + 2 * (3 * gamma)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro m _
      apply (abs_add_le _ _).trans
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul (hdA m) (hS m) (abs_nonneg _) (by positivity))
        (mul_le_mul (hA m) (hT m) (abs_nonneg _) (by norm_num))
    _ = _ := by simp; ring

end PoincareConjecture.Proofs.M47
