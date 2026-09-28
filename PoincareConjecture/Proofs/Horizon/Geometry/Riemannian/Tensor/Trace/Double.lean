import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.TraceRegularity

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

lemma covariantTensorDerivative_tensorTrace_tensorTrace
    (D : LeviCivitaData g) {k : ℕ} {T : CovariantTensorEvaluation n M (k + 4)}
    (hT : IsSmoothCovariantTensor T) (x : M) (u : TangentSpace (𝓡 n) x)
    (v : Fin k → TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (g.tensorTrace (g.tensorTrace T)) x (Fin.cons u v) =
      ∑ i, ∑ j, D.covariantTensorDerivative T x
        (Fin.cons u (Fin.cons (g.orthonormalBasis x i) (Fin.cons (g.orthonormalBasis x i)
          (Fin.cons (g.orthonormalBasis x j) (Fin.cons (g.orthonormalBasis x j) v))))) := by
  rw [D.covariantTensorDerivative_tensorTrace (hT.tensorTrace (g := g))]
  simp_rw [D.covariantTensorDerivative_tensorTrace hT]
  exact Finset.sum_comm

end PoincareConjecture.LeviCivitaData
