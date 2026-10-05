import PoincareLib.Geometry.Riemannian.Curvature.RicciContraction
import PoincareLib.Geometry.Riemannian.Tensor.Trace
import PoincareLib.Geometry.Riemannian.Tensor.Linearity
import PoincareLib.Geometry.Riemannian.Tensor.Algebra

/-! # The second covariant derivative of the Ricci contraction -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- Metric compatibility commutes a second covariant derivative with the
Ricci contraction, preserving both derivative inputs. -/
lemma secondCovariantTensorDerivative_ricciEvaluation_eq_sum_riemann
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    (a b c d : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (D.covariantTensorDerivative D.ricciEvaluation)
        x ![a, b, c, d] =
      ∑ i, D.covariantTensorDerivative (D.covariantTensorDerivative D.riemannEvaluation)
        x ![a, b, c, g.orthonormalBasis x i, d, g.orthonormalBasis x i] := by
  let σ : Equiv.Perm (Fin 5) := Equiv.ofBijective ![2, 3, 0, 4, 1] (by decide)
  let S : CovariantTensorEvaluation n M 5 := fun y z =>
    D.covariantTensorDerivative D.riemannEvaluation y (z ∘ σ)
  have hS : IsSmoothCovariantTensor S :=
    PoincareMT.IsSmoothCovariantTensor.perm (hD.2.2.1 _ _ hD.1) σ
  have heq : D.covariantTensorDerivative D.ricciEvaluation = g.tensorTrace S := by
    funext y z
    have hz : z = ![z 0, z 1, z 2] := by ext i; fin_cases i <;> rfl
    rw [hz, D.covariantTensorDerivative_ricciEvaluation_eq_sum_riemann hD]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    ext j
    fin_cases j <;> rfl
  rw [heq]
  have h := D.covariantTensorDerivative_tensorTrace hS x a ![b, c, d]
  rw [Matrix.Fin.cons_vecCons] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  rw [show S = (fun y z => D.covariantTensorDerivative D.riemannEvaluation y (z ∘ σ))
    from rfl, D.covariantTensorDerivative_reindex]
  congr 1
  ext j
  fin_cases j <;> rfl

end PoincareMT.LeviCivitaData
