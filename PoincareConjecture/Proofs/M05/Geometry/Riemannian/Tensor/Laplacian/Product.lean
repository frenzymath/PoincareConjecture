import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.ProductDerivative
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.Laplacian.Linearity

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private noncomputable def productDerivativePerm : Equiv.Perm (Fin 7) :=
  Equiv.ofBijective ![1, 2, 3, 4, 0, 5, 6] (by decide)

private lemma productDerivative_eq (D : LeviCivitaData g)
    {S : CovariantTensorEvaluation n M 4} {T : CovariantTensorEvaluation n M 2}
    (hS : IsSmoothCovariantTensor S) (hT : IsSmoothCovariantTensor T) :
    D.covariantTensorDerivative (tensorProduct S T) = fun x v =>
      tensorProduct (D.covariantTensorDerivative S) T x v +
      tensorProduct S (D.covariantTensorDerivative T) x (v ∘ productDerivativePerm) := by
  funext x v
  have hv : v = Fin.cons (v 0) (fun i : Fin 6 => v i.succ) := by
    ext i
    fin_cases i <;> rfl
  conv_lhs => rw [hv]
  rw [D.covariantTensorDerivative_tensorProduct hS hT]
  simp only [tensorProduct]
  congr 2 <;> congr 1 <;> ext i <;> fin_cases i <;> rfl

lemma iteratedCovariantTensorDerivative_tensorProduct_four_two
    (D : LeviCivitaData g)
    {S : CovariantTensorEvaluation n M 4} {T : CovariantTensorEvaluation n M 2}
    (hS : IsSmoothCovariantTensor S) (hT : IsSmoothCovariantTensor T)
    (hDS : IsSmoothCovariantTensor (D.covariantTensorDerivative S))
    (hDT : IsSmoothCovariantTensor (D.covariantTensorDerivative T))
    (x : M) (u w a b c d e f : TangentSpace (𝓡 n) x) :
    D.iteratedCovariantTensorDerivative (tensorProduct S T) 2 x ![u,w,a,b,c,d,e,f] =
      D.iteratedCovariantTensorDerivative S 2 x ![u,w,a,b,c,d] * T x ![e,f] +
      D.covariantTensorDerivative S x ![w,a,b,c,d] *
        D.covariantTensorDerivative T x ![u,e,f] +
      (D.covariantTensorDerivative S x ![u,a,b,c,d] *
        D.covariantTensorDerivative T x ![w,e,f] +
      S x ![a,b,c,d] * D.iteratedCovariantTensorDerivative T 2 x ![u,w,e,f]) := by
  simp only [iteratedCovariantTensorDerivative]
  rw [productDerivative_eq D hS hT,
    D.covariantTensorDerivative_add (isSmoothCovariantTensor_tensorProduct hDS hT)
      ((isSmoothCovariantTensor_tensorProduct hS hDT).perm productDerivativePerm)]
  dsimp only
  rw [D.covariantTensorDerivative_reindex]
  have hv : Fin.cons (![u,w,a,b,c,d,e,f] 0)
      (fun i => ![u,w,a,b,c,d,e,f] (productDerivativePerm i).succ) =
      ![u,a,b,c,d,w,e,f] := by
    ext i
    fin_cases i <;> rfl
  rw [hv]
  have h₁ := D.covariantTensorDerivative_tensorProduct hDS hT x u ![w,a,b,c,d,e,f]
  have h₂ := D.covariantTensorDerivative_tensorProduct hS hDT x u ![a,b,c,d,w,e,f]
  simp only [Matrix.Fin.cons_vecCons] at h₁ h₂
  rw [h₁, h₂]
  congr 2 <;> congr 1 <;> congr 1 <;> ext i <;> fin_cases i <;> rfl

lemma tensorLaplacian_tensorProduct_four_two
    (D : LeviCivitaData g)
    {S : CovariantTensorEvaluation n M 4} {T : CovariantTensorEvaluation n M 2}
    (hS : IsSmoothCovariantTensor S) (hT : IsSmoothCovariantTensor T)
    (hDS : IsSmoothCovariantTensor (D.covariantTensorDerivative S))
    (hDT : IsSmoothCovariantTensor (D.covariantTensorDerivative T))
    (x : M) (a b c d e f : TangentSpace (𝓡 n) x) :
    D.tensorLaplacian (tensorProduct S T) x ![a,b,c,d,e,f] =
      D.tensorLaplacian S x ![a,b,c,d] * T x ![e,f] +
      S x ![a,b,c,d] * D.tensorLaplacian T x ![e,f] +
      2 * ∑ i, D.covariantTensorDerivative S x ![g.orthonormalBasis x i,a,b,c,d] *
        D.covariantTensorDerivative T x ![g.orthonormalBasis x i,e,f] := by
  simp only [tensorLaplacian, Matrix.Fin.cons_vecCons]
  simp_rw [D.iteratedCovariantTensorDerivative_tensorProduct_four_two hS hT hDS hDT]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

private def derivativePerm {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    Equiv.Perm (Fin (k + 1)) where
  toFun := Fin.cases 0 (fun i => (σ i).succ)
  invFun := Fin.cases 0 (fun i => (σ.symm i).succ)
  left_inv := by intro i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  right_inv := by intro i; refine Fin.cases ?_ (fun j => ?_) i <;> simp

lemma tensorLaplacian_reindex {k : ℕ} (D : LeviCivitaData g)
    (T : CovariantTensorEvaluation n M k) (σ : Equiv.Perm (Fin k))
    (x : M) (v : Fin k → TangentSpace (𝓡 n) x) :
    D.tensorLaplacian (fun y w => T y (w ∘ σ)) x v =
      D.tensorLaplacian T x (v ∘ σ) := by
  have hD : D.covariantTensorDerivative (fun y w => T y (w ∘ σ)) =
      fun y w => D.covariantTensorDerivative T y (w ∘ derivativePerm σ) := by
    funext y w
    rw [D.covariantTensorDerivative_reindex]
    congr 1
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  simp only [tensorLaplacian, iteratedCovariantTensorDerivative, hD]
  apply Finset.sum_congr rfl
  intro i hi
  rw [D.covariantTensorDerivative_reindex]
  congr 1
  ext j
  refine Fin.cases ?_ (fun l => ?_) j
  · rfl
  · refine Fin.cases ?_ (fun q => ?_) l <;> rfl

end PoincareConjecture.LeviCivitaData
