import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Commutation.Laplacian.General
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Commutation.CurvatureAction.Three
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Commutation.Contractions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

lemma covariantTensorDerivative_tensorLaplacian_commutator_three
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    {T : CovariantTensorEvaluation n M 3} (hT : IsSmoothCovariantTensor T)
    (x : M) (a b c d : TangentSpace (𝓡 n) x) :
    let e := g.orthonormalBasis x
    D.covariantTensorDerivative (D.tensorLaplacian T) x ![a, b, c, d] -
        D.tensorLaplacian (D.covariantTensorDerivative T) x ![a, b, c, d] =
      2 * (∑ i, ∑ j, D.curvatureTensor x a (e i) b (e j) *
        D.covariantTensorDerivative T x ![e i, e j, c, d]) +
      2 * (∑ i, ∑ j, D.curvatureTensor x a (e i) c (e j) *
        D.covariantTensorDerivative T x ![e i, b, e j, d]) +
      2 * (∑ i, ∑ j, D.curvatureTensor x a (e i) d (e j) *
        D.covariantTensorDerivative T x ![e i, b, c, e j]) -
      (∑ i, D.ricci x a (e i) * D.covariantTensorDerivative T x ![e i, b, c, d]) +
      (∑ j, (D.covariantTensorDerivative D.ricciEvaluation x ![e j, a, b] -
        D.covariantTensorDerivative D.ricciEvaluation x ![b, a, e j]) * T x ![e j, c, d]) +
      (∑ j, (D.covariantTensorDerivative D.ricciEvaluation x ![e j, a, c] -
        D.covariantTensorDerivative D.ricciEvaluation x ![c, a, e j]) * T x ![b, e j, d]) +
      (∑ j, (D.covariantTensorDerivative D.ricciEvaluation x ![e j, a, d] -
        D.covariantTensorDerivative D.ricciEvaluation x ![d, a, e j]) * T x ![b, c, e j]) := by
  let e := g.orthonormalBasis x
  let A := D.covariantTensorDerivative T
  have hA := hD.2.2.1 _ _ hT
  have hupdate (p q r s w : TangentSpace (𝓡 n) x) :
      Function.update ![p, q, r, s] 0 w = ![w, q, r, s] ∧
      Function.update ![p, q, r, s] 1 w = ![p, w, r, s] ∧
      Function.update ![p, q, r, s] 2 w = ![p, q, w, s] ∧
      Function.update ![p, q, r, s] 3 w = ![p, q, r, w] := by
    constructor
    · ext i; fin_cases i <;> simp
    constructor
    · ext i; fin_cases i <;> simp
    constructor <;> (ext i; fin_cases i <;> simp)
  have hleft (i) : A x ![e i, D.curvature x a (e i) b, c, d] =
      ∑ j, D.curvatureTensor x a (e i) (e j) b * A x ![e i, e j, c, d] := by
    simpa only [hupdate] using
      D.tensor_curvature_slot_eq_sum hA x ![e i, b, c, d] 1 a (e i) b
  have hmiddle (i) : A x ![e i, b, D.curvature x a (e i) c, d] =
      ∑ j, D.curvatureTensor x a (e i) (e j) c * A x ![e i, b, e j, d] := by
    simpa only [hupdate] using
      D.tensor_curvature_slot_eq_sum hA x ![e i, b, c, d] 2 a (e i) c
  have hright (i) : A x ![e i, b, c, D.curvature x a (e i) d] =
      ∑ j, D.curvatureTensor x a (e i) (e j) d * A x ![e i, b, c, e j] := by
    simpa only [hupdate] using
      D.tensor_curvature_slot_eq_sum hA x ![e i, b, c, d] 3 a (e i) d
  have hact (f : TangentSpace (𝓡 n) x) :
      D.covariantCurvatureAction A x a f ![f, b, c, d] =
        A x ![D.curvature x a f f, b, c, d] + A x ![f, D.curvature x a f b, c, d] +
          A x ![f, b, D.curvature x a f c, d] + A x ![f, b, c, D.curvature x a f d] := by
    change (∑ i : Fin 4, A x (Function.update ![f, b, c, d] i
      (D.curvature x a f (![f, b, c, d] i)))) = _
    rw [Fin.sum_univ_four]
    simp only [
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      hupdate]
    rfl
  have hric := D.sum_curvature_cons_eq_ricci_mul hA x a ![b, c, d]
  simp only [Matrix.Fin.cons_vecCons] at hric
  have hdiv (s : TangentSpace (𝓡 n) x) (f : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ) :
      (∑ i, ∑ j, D.covariantTensorDerivative D.riemannEvaluation x
          ![e i, a, e i, e j, s] * f j) =
        ∑ j, (D.covariantTensorDerivative D.ricciEvaluation x ![s, a, e j] -
          D.covariantTensorDerivative D.ricciEvaluation x ![e j, a, s]) * f j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_mul]
    congr 1
    exact D.sum_covariantTensorDerivative_riemannEvaluation_divergence hD x a s (e j)
  have hraw := D.covariantTensorDerivative_tensorLaplacian_commutator_all_raw hD hT x a ![b, c, d]
  have htail (y : M) (z : Fin 5 → TangentSpace (𝓡 n) y) :
      (fun i : Fin 3 => z i.succ.succ) = ![z 2, z 3, z 4] := by
    ext i; fin_cases i <;> rfl
  dsimp only at hraw ⊢
  simp only [Matrix.Fin.cons_vecCons, htail] at hraw
  simp_rw [D.covariantTensorDerivative_curvature_action_three hD hT] at hraw
  change _ = -∑ i, (D.covariantCurvatureAction A x a (e i) ![e i, b, c, d] +
    ∑ j, (D.covariantTensorDerivative D.riemannEvaluation x ![e i, a, e i, e j, b] *
      T x ![e j, c, d] + D.curvatureTensor x a (e i) (e j) b * A x ![e i, e j, c, d] +
      D.covariantTensorDerivative D.riemannEvaluation x ![e i, a, e i, e j, c] *
      T x ![b, e j, d] + D.curvatureTensor x a (e i) (e j) c * A x ![e i, b, e j, d] +
      D.covariantTensorDerivative D.riemannEvaluation x ![e i, a, e i, e j, d] *
      T x ![b, c, e j] + D.curvatureTensor x a (e i) (e j) d * A x ![e i, b, c, e j])) at hraw
  simp_rw [hact, hleft, hmiddle, hright] at hraw
  simp only [Finset.sum_add_distrib] at hraw
  rw [hric, hdiv b (fun j => T x ![e j, c, d]),
    hdiv c (fun j => T x ![b, e j, d]), hdiv d (fun j => T x ![b, c, e j])] at hraw
  have hskew (i j : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)))
      (s : TangentSpace (𝓡 n) x) :
      D.curvatureTensor x a (e i) (e j) s = -D.curvatureTensor x a (e i) s (e j) :=
    (hD.2.2.2.1 x a (e i) (e j) s).1
  simp_rw [hskew] at hraw
  simp only [neg_mul, Finset.sum_neg_distrib, sub_mul, Finset.sum_sub_distrib] at hraw ⊢
  dsimp only [A, e] at hraw
  linarith only [hraw]

end PoincareConjecture.LeviCivitaData
