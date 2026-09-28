import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.Trace
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.Linearity
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.Algebra
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

lemma sum_secondCovariantTensorDerivative_eq_hessian_trace
    (D : LeviCivitaData g) {T : CovariantTensorEvaluation n M 2}
    (hT : IsSmoothCovariantTensor T)
    (hDT : IsSmoothCovariantTensor (D.covariantTensorDerivative T))
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    (∑ i, D.iteratedCovariantTensorDerivative T 2 x
      ![u, v, g.orthonormalBasis x i, g.orthonormalBasis x i]) =
      D.hessian
        (fun y => ∑ i, T y ![g.orthonormalBasis y i, g.orthonormalBasis y i])
        x u v := by
  let σ : Equiv.Perm (Fin 3) := (Equiv.swap 0 2).trans (Equiv.swap 0 1)
  let S : CovariantTensorEvaluation n M 3 :=
    fun y w => D.covariantTensorDerivative T y (w ∘ σ)
  let f : M → ℝ :=
    fun y => ∑ i, T y ![g.orthonormalBasis y i, g.orthonormalBasis y i]
  have hperm (y : M) (a b c : TangentSpace (𝓡 n) y) :
      ![a, b, c] ∘ σ = ![c, a, b] := by
    ext i
    fin_cases i <;> simp [σ, Equiv.swap_apply_def]
  have htrace : g.tensorTrace S = fun y w => mvfderiv (𝓡 n) f y (w 0) := by
    funext y w
    have hw : w = ![w 0] := by ext i; fin_cases i; rfl
    rw [hw]
    change (∑ i, S y ![g.orthonormalBasis y i, g.orthonormalBasis y i, w 0]) = _
    simp only [S, hperm]
    exact D.sum_covariantTensorDerivative_eq_mvfderiv_metricTrace hT y (w 0)
  have hderiv (a b : TangentSpace (𝓡 n) x) :
      D.covariantTensorDerivative S x ![u, a, b, v] =
        D.iteratedCovariantTensorDerivative T 2 x ![u, v, a, b] := by
    rw [show S = (fun y w => D.covariantTensorDerivative T y (w ∘ σ)) from rfl,
      D.covariantTensorDerivative_reindex]
    change D.covariantTensorDerivative (D.covariantTensorDerivative T) x
      (Fin.cons u (![a, b, v] ∘ σ)) = _
    rw [hperm]
    rfl
  have h := D.covariantTensorDerivative_tensorTrace (hDT.perm σ) x u ![v]
  change D.covariantTensorDerivative (g.tensorTrace S) x ![u, v] =
    ∑ i, D.covariantTensorDerivative S x
      ![u, g.orthonormalBasis x i, g.orthonormalBasis x i, v] at h
  rw [htrace] at h
  simp only [hderiv] at h
  rw [← h]
  simp [covariantTensorDerivative, hessian, hessianOnFields, f]

lemma sum_tensorLaplacian_eq_laplacian_trace
    (D : LeviCivitaData g) {T : CovariantTensorEvaluation n M 2}
    (hT : IsSmoothCovariantTensor T)
    (hDT : IsSmoothCovariantTensor (D.covariantTensorDerivative T)) (x : M) :
    (∑ i, D.tensorLaplacian T x ![g.orthonormalBasis x i, g.orthonormalBasis x i]) =
      D.laplacian
        (fun y => ∑ i, T y ![g.orthonormalBasis y i, g.orthonormalBasis y i]) x := by
  unfold tensorLaplacian laplacian
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact D.sum_secondCovariantTensorDerivative_eq_hessian_trace hT hDT x
    (g.orthonormalBasis x i) (g.orthonormalBasis x i)

lemma sum_tensorLaplacian_ricci_eq_laplacian_scalar
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M) :
    (∑ i, D.tensorLaplacian D.ricciEvaluation x
      ![g.orthonormalBasis x i, g.orthonormalBasis x i]) =
      D.laplacian D.scalarCurvature x := by
  exact D.sum_tensorLaplacian_eq_laplacian_trace hD.2.1 (hD.2.2.1 _ _ hD.2.1) x

end PoincareConjecture.LeviCivitaData
