import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Spacetime
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Evolution.P
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Tensor.HeatGradient.Three

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

theorem tensorHeatOperator_covariantHamiltonP_commutator
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M)
    (a b c d : TangentSpace (𝓡 n) x) :
    let D := F.connection t
    let e := (F.metric t).orthonormalBasis x
    let P : ℝ → CovariantTensorEvaluation n M 3 := fun s y z =>
      hamiltonP (F.connection s) y (z 0) (z 1) (z 2)
    F.tensorHeatOperator (fun s => (F.connection s).covariantTensorDerivative (P s)) t x ![a, b, c, d] -
      D.covariantTensorDerivative (F.tensorHeatOperator P t) x ![a, b, c, d] =
      2 * (∑ i, ∑ j, D.curvatureTensor x a (e i) b (e j) *
        D.covariantTensorDerivative (P t) x ![e i, e j, c, d]) +
      2 * (∑ i, ∑ j, D.curvatureTensor x a (e i) c (e j) *
        D.covariantTensorDerivative (P t) x ![e i, b, e j, d]) +
      2 * (∑ i, ∑ j, D.curvatureTensor x a (e i) d (e j) *
        D.covariantTensorDerivative (P t) x ![e i, b, c, e j]) := by
  let P : ℝ → CovariantTensorEvaluation n M 3 := fun s y z =>
    hamiltonP (F.connection s) y (z 0) (z 1) (z 2)
  let W : ℝ → CovariantTensorEvaluation n M 3 := fun s y z =>
    deriv (fun r => P r y z) s
  apply F.tensorHeatOperator_covariantTensorDerivative_commutator_three (W := W) hC ht
  · exact fun s => hamiltonP_isSmoothCovariantTensor (F.connection s)
      (hC.tensor_calculus n M (F.metric s) (F.connection s))
  · exact fun _ _ hX => contMDiffAt_hamiltonP_fields hC F ht hX
  · intro y z
    exact (hasDerivAt_hamiltonP_evolution hC F ht y (z 0) (z 1) (z 2)).differentiableAt.hasDerivAt

end Poincare.RicciFlow.Harnack
