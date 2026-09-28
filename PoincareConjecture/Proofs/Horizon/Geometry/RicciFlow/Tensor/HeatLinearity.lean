import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Tensor.HeatGradient
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Laplacian.Linearity






set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {k : ℕ}

lemma tensorHeatOperator_add
    (F : RicciFlow n M J) {S T : ℝ → CovariantTensorEvaluation n M k} {t : ℝ}
    (hS : IsSmoothCovariantTensor (S t)) (hT : IsSmoothCovariantTensor (T t))
    (hDS : IsSmoothCovariantTensor ((F.connection t).covariantTensorDerivative (S t)))
    (hDT : IsSmoothCovariantTensor ((F.connection t).covariantTensorDerivative (T t)))
    (x : M) (v : Fin k → TangentSpace (𝓡 n) x)
    (hdS : DifferentiableAt ℝ (fun s => S s x v) t)
    (hdT : DifferentiableAt ℝ (fun s => T s x v) t) :
    F.tensorHeatOperator (fun s y z => S s y z + T s y z) t x v =
      F.tensorHeatOperator S t x v + F.tensorHeatOperator T t x v := by
  unfold tensorHeatOperator
  have hd := (hdS.hasDerivAt.add hdT.hasDerivAt).deriv
  change deriv (fun s => S s x v + T s x v) t =
    deriv (fun s => S s x v) t + deriv (fun s => T s x v) t at hd
  rw [hd, (F.connection t).tensorLaplacian_add hS hT hDS hDT]
  simp only [LeviCivitaData.ricciTensorAction, mul_add, Finset.sum_add_distrib]
  ring

end PoincareConjecture.RicciFlow
