import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Harnack.Matrix.Tensors
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.RicciContraction
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.RicciContraction.SecondDerivative
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.NormBounds
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.LaplacianTrace










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private lemma tangentNorm_basis (x : M)
    (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
    g.tangentNorm x (g.orthonormalBasis x i) = 1 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change Real.sqrt (inner ℝ (g.orthonormalBasis x i) (g.orthonormalBasis x i)) = 1
  rw [real_inner_self_eq_norm_sq, (g.orthonormalBasis x).norm_eq_one]
  norm_num


lemma abs_curvatureTensor_le_curvatureDerivativeNorm_zero
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (a b c d : TangentSpace (𝓡 n) x) :
    |D.curvatureTensor x a b c d| ≤ D.curvatureDerivativeNorm 0 x *
      g.tangentNorm x a * g.tangentNorm x b *
      g.tangentNorm x c * g.tangentNorm x d := by
  obtain ⟨A, hA⟩ := hD.1.1 x
  simpa [curvatureDerivativeNorm, iteratedCovariantTensorDerivative,
    riemannEvaluation, Fin.prod_univ_succ, mul_assoc] using
    abs_tensor_evaluation_le_tensorNorm g D.riemannEvaluation x A hA ![a, b, c, d]


lemma abs_ricci_le_curvatureDerivativeNorm_zero
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    |D.ricci x u v| ≤ (n : ℝ) * D.curvatureDerivativeNorm 0 x *
      g.tangentNorm x u * g.tangentNorm x v := by
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    unfold TangentSpace
    simp
  unfold ricci
  calc
    _ ≤ ∑ i, |D.curvatureTensor x u (g.orthonormalBasis x i)
        v (g.orthonormalBasis x i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        D.curvatureDerivativeNorm 0 x * g.tangentNorm x u * g.tangentNorm x v := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [tangentNorm_basis, mul_one] using
        D.abs_curvatureTensor_le_curvatureDerivativeNorm_zero hD x u
          (g.orthonormalBasis x i) v (g.orthonormalBasis x i)
    _ = _ := by simp [hdim, mul_assoc]



lemma abs_secondCovariantTensorDerivative_ricci_le_curvatureDerivativeNorm
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (a b u v : TangentSpace (𝓡 n) x) :
    |D.covariantTensorDerivative (D.covariantTensorDerivative D.ricciEvaluation)
        x ![a, b, u, v]| ≤ (n : ℝ) * D.curvatureDerivativeNorm 2 x *
      g.tangentNorm x a * g.tangentNorm x b *
      g.tangentNorm x u * g.tangentNorm x v := by
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    unfold TangentSpace
    simp
  obtain ⟨A, hA⟩ := (hD.2.2.1 _ _ (hD.2.2.1 _ _ hD.1)).1 x
  rw [D.secondCovariantTensorDerivative_ricciEvaluation_eq_sum_riemann hD]
  calc
    _ ≤ ∑ i, |D.covariantTensorDerivative (D.covariantTensorDerivative
        D.riemannEvaluation) x ![a, b, u, g.orthonormalBasis x i,
          v, g.orthonormalBasis x i]| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        D.curvatureDerivativeNorm 2 x * g.tangentNorm x a * g.tangentNorm x b *
          g.tangentNorm x u * g.tangentNorm x v := by
      apply Finset.sum_le_sum
      intro i _
      have h := abs_tensor_evaluation_le_tensorNorm g
        (D.covariantTensorDerivative (D.covariantTensorDerivative D.riemannEvaluation))
        x A hA ![a, b, u, g.orthonormalBasis x i, v, g.orthonormalBasis x i]
      simpa only [curvatureDerivativeNorm, iteratedCovariantTensorDerivative,
        Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
        Fin.prod_univ_zero, tangentNorm_basis, mul_one, one_mul, mul_assoc] using h
    _ = _ := by simp [hdim, mul_assoc]



lemma abs_tensorLaplacian_ricci_le_curvatureDerivativeNorm
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    |D.tensorLaplacian D.ricciEvaluation x ![u, v]| ≤
      (n : ℝ) ^ 2 * D.curvatureDerivativeNorm 2 x *
        g.tangentNorm x u * g.tangentNorm x v := by
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    unfold TangentSpace
    simp
  unfold tensorLaplacian
  calc
    _ ≤ ∑ i, |D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x
        ![g.orthonormalBasis x i, g.orthonormalBasis x i, u, v]| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        (n : ℝ) * D.curvatureDerivativeNorm 2 x *
          g.tangentNorm x u * g.tangentNorm x v := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [iteratedCovariantTensorDerivative, tangentNorm_basis, mul_one] using
        D.abs_secondCovariantTensorDerivative_ricci_le_curvatureDerivativeNorm hD x
          (g.orthonormalBasis x i) (g.orthonormalBasis x i) u v
    _ = _ := by simp [hdim]; ring



lemma abs_hessian_scalar_le_curvatureDerivativeNorm
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    |D.hessian D.scalarCurvature x u v| ≤
      (n : ℝ) ^ 2 * D.curvatureDerivativeNorm 2 x *
        g.tangentNorm x u * g.tangentNorm x v := by
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    unfold TangentSpace
    simp
  have he := D.sum_secondCovariantTensorDerivative_eq_hessian_trace
    hD.2.1 (hD.2.2.1 _ _ hD.2.1) x u v
  change (∑ i, D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x
    ![u, v, g.orthonormalBasis x i, g.orthonormalBasis x i]) =
      D.hessian D.scalarCurvature x u v at he
  rw [← he]
  calc
    _ ≤ ∑ i, |D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x
        ![u, v, g.orthonormalBasis x i, g.orthonormalBasis x i]| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        (n : ℝ) * D.curvatureDerivativeNorm 2 x *
          g.tangentNorm x u * g.tangentNorm x v := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [iteratedCovariantTensorDerivative, tangentNorm_basis, mul_one] using
        D.abs_secondCovariantTensorDerivative_ricci_le_curvatureDerivativeNorm hD x
          u v (g.orthonormalBasis x i) (g.orthonormalBasis x i)
    _ = _ := by simp [hdim]; ring



lemma abs_laplacian_scalar_le_curvatureDerivativeNorm
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M) :
    |D.laplacian D.scalarCurvature x| ≤
      (n : ℝ) ^ 3 * D.curvatureDerivativeNorm 2 x := by
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    unfold TangentSpace
    simp
  unfold laplacian
  calc
    _ ≤ ∑ i, |D.hessian D.scalarCurvature x
        (g.orthonormalBasis x i) (g.orthonormalBasis x i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        (n : ℝ) ^ 2 * D.curvatureDerivativeNorm 2 x := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [tangentNorm_basis, mul_one] using
        D.abs_hessian_scalar_le_curvatureDerivativeNorm hD x
          (g.orthonormalBasis x i) (g.orthonormalBasis x i)
    _ = _ := by simp [hdim]; ring



lemma abs_covariantTensorDerivative_ricci_le_curvatureDerivativeNorm
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (u v w : TangentSpace (𝓡 n) x) :
    |D.covariantTensorDerivative D.ricciEvaluation x ![u, v, w]| ≤
      (n : ℝ) * D.curvatureDerivativeNorm 1 x *
        g.tangentNorm x u * g.tangentNorm x v * g.tangentNorm x w := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  have hb (i) : g.tangentNorm x (b i) = 1 := by
    change Real.sqrt (inner ℝ (b i) (b i)) = 1
    rw [real_inner_self_eq_norm_sq, b.norm_eq_one]
    norm_num
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    unfold TangentSpace
    simp
  obtain ⟨A, hA⟩ := (hD.2.2.1 _ _ hD.1).1 x
  have hterm (i) :
      |D.covariantTensorDerivative D.riemannEvaluation x ![u, v, b i, w, b i]| ≤
        D.curvatureDerivativeNorm 1 x *
          g.tangentNorm x u * g.tangentNorm x v * g.tangentNorm x w := by
    have h := abs_tensor_evaluation_le_tensorNorm g
      (D.covariantTensorDerivative D.riemannEvaluation) x A hA ![u, v, b i, w, b i]
    simpa only [curvatureDerivativeNorm, iteratedCovariantTensorDerivative,
      Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.prod_univ_zero, hb, mul_one, one_mul, mul_assoc] using h
  rw [D.covariantTensorDerivative_ricciEvaluation_eq_sum_riemann hD]
  calc
    _ ≤ ∑ i, |D.covariantTensorDerivative D.riemannEvaluation x
        ![u, v, b i, w, b i]| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        D.curvatureDerivativeNorm 1 x *
          g.tangentNorm x u * g.tangentNorm x v * g.tangentNorm x w :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = _ := by simp [hdim, mul_assoc]

end PoincareConjecture.LeviCivitaData

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}



lemma abs_hamiltonP_le_curvatureDerivativeNorm
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (u v w : TangentSpace (𝓡 n) x) :
    |hamiltonP D x u v w| ≤
      2 * (n : ℝ) * D.curvatureDerivativeNorm 1 x *
        g.tangentNorm x u * g.tangentNorm x v * g.tangentNorm x w := by
  have hu := D.abs_covariantTensorDerivative_ricci_le_curvatureDerivativeNorm hD x u v w
  have hv := D.abs_covariantTensorDerivative_ricci_le_curvatureDerivativeNorm hD x v u w
  have hsub := abs_sub
    (D.covariantTensorDerivative D.ricciEvaluation x ![u, v, w])
    (D.covariantTensorDerivative D.ricciEvaluation x ![v, u, w])
  have h := hsub.trans (add_le_add hu hv)
  unfold hamiltonP
  nlinarith only [h]



lemma abs_hamiltonM_sub_ricci_le_curvatureDerivativeNorm
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (τ : ℝ) (x : M) (u v : TangentSpace (𝓡 n) x) :
    |hamiltonM D τ x u v - D.ricci x u v / (2 * τ)| ≤
      (2 * (n : ℝ) ^ 2 * D.curvatureDerivativeNorm 2 x +
        3 * (n : ℝ) ^ 3 * (D.curvatureDerivativeNorm 0 x) ^ 2) *
          g.tangentNorm x u * g.tangentNorm x v := by
  let b := g.orthonormalBasis x
  let K := D.curvatureDerivativeNorm 0 x
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  have hu : 0 ≤ g.tangentNorm x u := Real.sqrt_nonneg _
  have hv : 0 ≤ g.tangentNorm x v := Real.sqrt_nonneg _
  have hb (i) : g.tangentNorm x (b i) = 1 :=
    PoincareConjecture.LeviCivitaData.tangentNorm_basis x i
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    unfold TangentSpace
    simp
  have hcurv (i j) : |D.curvatureTensor x (b i) u (b j) v| ≤
      K * g.tangentNorm x u * g.tangentNorm x v := by
    simpa only [hb, mul_one] using
      D.abs_curvatureTensor_le_curvatureDerivativeNorm_zero hD x (b i) u (b j) v
  have hric (i j) : |D.ricci x (b i) (b j)| ≤ (n : ℝ) * K := by
    simpa only [hb, mul_one] using D.abs_ricci_le_curvatureDerivativeNorm_zero hD x (b i) (b j)
  have hRmRic : |∑ i, ∑ j, D.curvatureTensor x (b i) u (b j) v * D.ricci x (b i) (b j)| ≤
      (n : ℝ) ^ 3 * K ^ 2 * g.tangentNorm x u * g.tangentNorm x v := by
    calc
      _ ≤ ∑ i, |∑ j, D.curvatureTensor x (b i) u (b j) v * D.ricci x (b i) (b j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |D.curvatureTensor x (b i) u (b j) v * D.ricci x (b i) (b j)| :=
        Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
          ∑ _j : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
            (n : ℝ) * K ^ 2 * g.tangentNorm x u * g.tangentNorm x v := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        have h := mul_le_mul (hcurv i j) (hric i j) (abs_nonneg _) (by positivity)
        nlinarith only [h]
      _ = _ := by simp [hdim]; ring
  have hRicSq : |∑ i, D.ricci x u (b i) * D.ricci x (b i) v| ≤
      (n : ℝ) ^ 3 * K ^ 2 * g.tangentNorm x u * g.tangentNorm x v := by
    calc
      _ ≤ ∑ i, |D.ricci x u (b i) * D.ricci x (b i) v| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
          (n : ℝ) ^ 2 * K ^ 2 * g.tangentNorm x u * g.tangentNorm x v := by
        apply Finset.sum_le_sum
        intro i _
        have h₁ := D.abs_ricci_le_curvatureDerivativeNorm_zero hD x u (b i)
        have h₂ := D.abs_ricci_le_curvatureDerivativeNorm_zero hD x (b i) v
        simp only [hb, mul_one] at h₁ h₂
        rw [abs_mul]
        have h := mul_le_mul h₁ h₂ (abs_nonneg _) (by positivity)
        nlinarith only [h]
      _ = _ := by simp [hdim]; ring
  have hL := D.abs_tensorLaplacian_ricci_le_curvatureDerivativeNorm hD x u v
  have hH := D.abs_hessian_scalar_le_curvatureDerivativeNorm hD x u v
  have hC₂ : 0 ≤ (n : ℝ) ^ 2 * D.curvatureDerivativeNorm 2 x *
      g.tangentNorm x u * g.tangentNorm x v := by
    have h₂ : 0 ≤ D.curvatureDerivativeNorm 2 x := Real.sqrt_nonneg _
    positivity
  have htriangle := abs_add_le
    (D.tensorLaplacian D.ricciEvaluation x ![u, v] - D.hessian D.scalarCurvature x u v / 2)
    (2 * (∑ i, ∑ j, D.curvatureTensor x (b i) u (b j) v * D.ricci x (b i) (b j)) -
      ∑ i, D.ricci x u (b i) * D.ricci x (b i) v)
  have hdiff := abs_sub (D.tensorLaplacian D.ricciEvaluation x ![u, v])
    (D.hessian D.scalarCurvature x u v / 2)
  have halg := abs_sub
    (2 * (∑ i, ∑ j, D.curvatureTensor x (b i) u (b j) v * D.ricci x (b i) (b j)))
    (∑ i, D.ricci x u (b i) * D.ricci x (b i) v)
  norm_num only [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hdiff halg
  unfold hamiltonM
  dsimp only
  rw [add_sub_cancel_right]
  change |_ + (2 * (∑ i, ∑ j, D.curvatureTensor x (b i) u (b j) v *
    D.ricci x (b i) (b j)) - ∑ i, D.ricci x u (b i) * D.ricci x (b i) v)| ≤ _
  dsimp only [K] at hRmRic hRicSq
  nlinarith only [htriangle, hdiff, halg, hL, hH, hRmRic, hRicSq, hC₂]



lemma hamiltonM_lower_bound_of_nonnegative_ricci
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    {τ : ℝ} (hτ : 0 ≤ τ) (x : M) (v : TangentSpace (𝓡 n) x)
    (hRic : 0 ≤ D.ricci x v v) :
    -(2 * (n : ℝ) ^ 2 * D.curvatureDerivativeNorm 2 x +
        3 * (n : ℝ) ^ 3 * (D.curvatureDerivativeNorm 0 x) ^ 2) *
      (g.tangentNorm x v) ^ 2 ≤ hamiltonM D τ x v v := by
  have h := (abs_le.mp (abs_hamiltonM_sub_ricci_le_curvatureDerivativeNorm D hD τ x v v)).1
  have ht : 0 ≤ D.ricci x v v / (2 * τ) := div_nonneg hRic (by positivity)
  nlinarith only [h, ht]

end Poincare.RicciFlow.Harnack
