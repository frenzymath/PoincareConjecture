import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Tensor.HeatGradient
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Laplacian.Linearity


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {k : ℕ}

lemma tensorHeatOperator_time_mul
    (F : RicciFlow n M J) {T : ℝ → CovariantTensorEvaluation n M k}
    {f : ℝ → ℝ} {f' t : ℝ} (hf : HasDerivAt f f' t)
    (hT : IsSmoothCovariantTensor (T t))
    (hDT : IsSmoothCovariantTensor ((F.connection t).covariantTensorDerivative (T t)))
    (x : M) (v : Fin k → TangentSpace (𝓡 n) x)
    (hd : DifferentiableAt ℝ (fun s => T s x v) t) :
    F.tensorHeatOperator (fun s y z => f s * T s y z) t x v =
      f t * F.tensorHeatOperator T t x v + f' * T t x v := by
  have hact : (F.connection t).ricciTensorAction (fun y z => f t * T t y z) x v =
      f t * (F.connection t).ricciTensorAction (T t) x v := by
    simp only [LeviCivitaData.ricciTensorAction, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold tensorHeatOperator
  have hprod := (hf.mul hd.hasDerivAt).deriv
  simp only [Pi.mul_def] at hprod
  rw [hprod, hact,
    (F.connection t).tensorLaplacian_const_mul hT hDT]
  ring

end PoincareConjecture.RicciFlow
