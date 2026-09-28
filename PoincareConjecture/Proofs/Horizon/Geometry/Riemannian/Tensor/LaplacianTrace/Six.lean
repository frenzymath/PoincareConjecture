import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.LaplacianTrace


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

lemma secondCovariantTensorDerivative_tensorTrace_six
    (D : LeviCivitaData g) {T : CovariantTensorEvaluation n M 6}
    (hT : IsSmoothCovariantTensor T)
    (hDT : IsSmoothCovariantTensor (D.covariantTensorDerivative T))
    (x : M) (a b c d e f : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (D.covariantTensorDerivative (g.tensorTrace T)) x
        ![a, b, c, d, e, f] =
      ∑ i, D.covariantTensorDerivative (D.covariantTensorDerivative T) x
        ![a, b, g.orthonormalBasis x i, g.orthonormalBasis x i, c, d, e, f] := by
  let σ : Equiv.Perm (Fin 7) := Equiv.ofBijective ![2, 0, 1, 3, 4, 5, 6] (by decide)
  let S : CovariantTensorEvaluation n M 7 :=
    fun y z => D.covariantTensorDerivative T y (z ∘ σ)
  have hp (y : M) (p q r s t u v : TangentSpace (𝓡 n) y) :
      ![p, q, r, s, t, u, v] ∘ σ = ![r, p, q, s, t, u, v] := by
    ext i; fin_cases i <;> rfl
  have htrace : D.covariantTensorDerivative (g.tensorTrace T) = g.tensorTrace S := by
    funext y z
    have hz : ![z 0, z 1, z 2, z 3, z 4] = z := by ext i; fin_cases i <;> rfl
    rw [← hz]
    have h := D.covariantTensorDerivative_tensorTrace hT y (z 0) ![z 1, z 2, z 3, z 4]
    simpa only [Matrix.Fin.cons_vecCons, RiemannianMetric.tensorTrace, S, hp] using h
  rw [htrace]
  have h := D.covariantTensorDerivative_tensorTrace (hDT.perm σ) x a ![b, c, d, e, f]
  simp only [Matrix.Fin.cons_vecCons] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  rw [D.covariantTensorDerivative_reindex]
  congr 1
  ext j; fin_cases j <;> rfl

lemma tensorLaplacian_tensorTrace_six
    (D : LeviCivitaData g) {T : CovariantTensorEvaluation n M 6}
    (hT : IsSmoothCovariantTensor T)
    (hDT : IsSmoothCovariantTensor (D.covariantTensorDerivative T))
    (x : M) (a b c d : TangentSpace (𝓡 n) x) :
    D.tensorLaplacian (g.tensorTrace T) x ![a, b, c, d] =
      g.tensorTrace (D.tensorLaplacian T) x ![a, b, c, d] := by
  change (∑ i, D.covariantTensorDerivative (D.covariantTensorDerivative (g.tensorTrace T)) x
    ![g.orthonormalBasis x i, g.orthonormalBasis x i, a, b, c, d]) =
      ∑ j, ∑ i, D.covariantTensorDerivative (D.covariantTensorDerivative T) x
        ![g.orthonormalBasis x i, g.orthonormalBasis x i,
          g.orthonormalBasis x j, g.orthonormalBasis x j, a, b, c, d]
  simp only [D.secondCovariantTensorDerivative_tensorTrace_six hT hDT]
  exact Finset.sum_comm

end PoincareConjecture.LeviCivitaData
