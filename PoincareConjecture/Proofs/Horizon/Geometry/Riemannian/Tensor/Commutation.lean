import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Operations
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.DerivativeOnFields
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Commutation.SecondDerivative
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Hessian.Tensor
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Hessian.Symmetry










set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Filter

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}



lemma iteratedCovariantTensorDerivative_scalar_swap
    (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (u v : TangentSpace (𝓡 n) x) :
    D.iteratedCovariantTensorDerivative (fun y _ => f y) 2 x ![u, v] =
      D.iteratedCovariantTensorDerivative (fun y _ => f y) 2 x ![v, u] := by
  let T₀ : CovariantTensorEvaluation n M 0 := fun y _ => f y
  have hfirst : D.covariantTensorDerivative T₀ =
      PoincareConjecture.differentialEvaluation f := by
    funext y z
    simp [T₀, covariantTensorDerivative, PoincareConjecture.differentialEvaluation]
  change D.covariantTensorDerivative (D.covariantTensorDerivative T₀) x ![u, v] =
    D.covariantTensorDerivative (D.covariantTensorDerivative T₀) x ![v, u]
  rw [hfirst]
  rw [← D.hessian_eq_covariantTensorDerivative f x u v,
    ← D.hessian_eq_covariantTensorDerivative f x v u]
  exact D.hessian_symm hf x u v






noncomputable def covariantCurvatureAction (D : LeviCivitaData g) {k : ℕ}
    (T : CovariantTensorEvaluation n M k) (x : M)
    (u v : TangentSpace (𝓡 n) x) (w : Fin k → TangentSpace (𝓡 n) x) : ℝ :=
  ∑ i, T x (Function.update w i (D.curvature x u v (w i)))

lemma covariantTensorDerivative_commutator_two
    (D : LeviCivitaData g) {T : CovariantTensorEvaluation n M 2}
    (hT : IsSmoothCovariantTensor T) (x : M)
    (a b c d : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (D.covariantTensorDerivative T) x ![a, b, c, d] -
      D.covariantTensorDerivative (D.covariantTensorDerivative T) x ![b, a, c, d] =
      -T x ![D.curvature x a b c, d] - T x ![c, D.curvature x a b d] := by
  have h := D.covariantTensorDerivative_commutator hT x a b ![c, d]
  have h0 : Function.update ![c, d] 0 (D.curvature x a b c) =
      ![D.curvature x a b c, d] := by ext i; fin_cases i <;> simp
  have h1 : Function.update ![c, d] 1 (D.curvature x a b d) =
      ![c, D.curvature x a b d] := by ext i; fin_cases i <;> simp
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.Fin.cons_vecCons, h0, h1, neg_add_rev, sub_eq_add_neg, add_comm] using h

@[simp]
lemma covariantCurvatureAction_zero (D : LeviCivitaData g)
    (T : CovariantTensorEvaluation n M 0) (x : M)
    (u v : TangentSpace (𝓡 n) x) (w : Fin 0 → TangentSpace (𝓡 n) x) :
    D.covariantCurvatureAction T x u v w = 0 := by
  simp [covariantCurvatureAction]

lemma covariantCurvatureAction_three (D : LeviCivitaData g)
    (T : CovariantTensorEvaluation n M 3) (x : M)
    (u v a b c : TangentSpace (𝓡 n) x) :
    D.covariantCurvatureAction T x u v ![a, b, c] =
      T x ![D.curvature x u v a, b, c] +
        T x ![a, D.curvature x u v b, c] +
          T x ![a, b, D.curvature x u v c] := by
  simp only [covariantCurvatureAction, Fin.sum_univ_three]
  change T x (Function.update ![a, b, c] 0 (D.curvature x u v a)) +
      T x (Function.update ![a, b, c] 1 (D.curvature x u v b)) +
        T x (Function.update ![a, b, c] 2 (D.curvature x u v c)) = _
  have h0 : Function.update ![a, b, c] 0 (D.curvature x u v a) =
      ![D.curvature x u v a, b, c] := by
    ext i
    fin_cases i <;> simp
  have h1 : Function.update ![a, b, c] 1 (D.curvature x u v b) =
      ![a, D.curvature x u v b, c] := by
    ext i
    fin_cases i <;> simp
  have h2 : Function.update ![a, b, c] 2 (D.curvature x u v c) =
      ![a, b, D.curvature x u v c] := by
    ext i
    fin_cases i <;> simp
  rw [h0, h1, h2]

lemma neg_covariantCurvatureAction_three (D : LeviCivitaData g)
    (T : CovariantTensorEvaluation n M 3) (x : M)
    (u v a b c : TangentSpace (𝓡 n) x) :
    -D.covariantCurvatureAction T x u v ![a, b, c] =
      -T x ![D.curvature x u v a, b, c] -
        T x ![a, D.curvature x u v b, c] -
          T x ![a, b, D.curvature x u v c] := by
  rw [D.covariantCurvatureAction_three T x u v a b c]
  ring


lemma covariantCurvatureAction_swap
    (D : LeviCivitaData g) {k : ℕ} (T : CovariantTensorEvaluation n M k)
    (hT : IsSmoothCovariantTensor T)
    (hR : ∀ (x : M) (u v z : TangentSpace (𝓡 n) x),
      D.curvature x v u z = -D.curvature x u v z)
    (x : M) (u v : TangentSpace (𝓡 n) x)
    (w : Fin k → TangentSpace (𝓡 n) x) :
    D.covariantCurvatureAction T x v u w =
      -D.covariantCurvatureAction T x u v w := by
  simp only [covariantCurvatureAction]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hR]
  obtain ⟨A, hA⟩ := hT.1 x
  rw [hA, hA]
  exact A.map_update_neg w i (D.curvature x u v (w i))

end PoincareConjecture.LeviCivitaData
