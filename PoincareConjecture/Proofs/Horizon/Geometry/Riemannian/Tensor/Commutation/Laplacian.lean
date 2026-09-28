import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Commutation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Trace
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Linearity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Algebra
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Commutation.CurvatureAction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Commutation.Contractions








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


lemma covariantTensorDerivative_tensorLaplacian_commutator_raw
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    {T : CovariantTensorEvaluation n M 2} (hT : IsSmoothCovariantTensor T)
    (x : M) (a b c : TangentSpace (𝓡 n) x) :
    let e := g.orthonormalBasis x
    let S : CovariantTensorEvaluation n M 4 := fun y z =>
      T y ![D.curvature y (z 0) (z 1) (z 2), z 3] +
        T y ![z 2, D.curvature y (z 0) (z 1) (z 3)]
    D.covariantTensorDerivative (D.tensorLaplacian T) x ![a, b, c] -
        D.tensorLaplacian (D.covariantTensorDerivative T) x ![a, b, c] =
      -∑ i, (D.covariantTensorDerivative T x ![D.curvature x a (e i) (e i), b, c] +
        D.covariantTensorDerivative T x ![e i, D.curvature x a (e i) b, c] +
        D.covariantTensorDerivative T x ![e i, b, D.curvature x a (e i) c] +
        D.covariantTensorDerivative S x ![e i, a, e i, b, c]) := by
  let S : CovariantTensorEvaluation n M 4 := fun y z =>
    T y ![D.curvature y (z 0) (z 1) (z 2), z 3] +
      T y ![z 2, D.curvature y (z 0) (z 1) (z 3)]
  let A := D.covariantTensorDerivative T
  let B := D.covariantTensorDerivative A
  have hA := hD.2.2.1 _ _ hT
  have hB := hD.2.2.1 _ _ hA
  have hperm (y : M) (z : Fin 4 → TangentSpace (𝓡 n) y) :
      z ∘ Equiv.swap 0 1 = ![z 1, z 0, z 2, z 3] := by
    ext i
    fin_cases i <;> simp [Equiv.swap_apply_def]
  have hS : S = fun y z => B y (z ∘ Equiv.swap 0 1) - B y z := by
    funext y z
    have h := D.covariantTensorDerivative_commutator_two hT y (z 0) (z 1) (z 2) (z 3)
    have hz : ![z 0, z 1, z 2, z 3] = z := by ext i; fin_cases i <;> rfl
    simp only [S, hperm]
    dsimp only [B, A]
    rw [hz] at h
    linarith only [h]
  have hDS (d p q r s : TangentSpace (𝓡 n) x) :
      D.covariantTensorDerivative S x ![d, p, q, r, s] =
        D.covariantTensorDerivative B x ![d, q, p, r, s] -
          D.covariantTensorDerivative B x ![d, p, q, r, s] := by
    rw [hS, D.covariantTensorDerivative_sub (hB.perm (Equiv.swap 0 1)) hB]
    dsimp only
    rw [D.covariantTensorDerivative_reindex]
    congr 2
    ext i
    fin_cases i <;> simp [Equiv.swap_apply_def] <;> rfl
  have hpoint (d : TangentSpace (𝓡 n) x) :
      D.covariantTensorDerivative B x ![a, d, d, b, c] -
        D.covariantTensorDerivative B x ![d, d, a, b, c] =
      -(A x ![D.curvature x a d d, b, c] + A x ![d, D.curvature x a d b, c] +
        A x ![d, b, D.curvature x a d c] + D.covariantTensorDerivative S x ![d, a, d, b, c]) := by
    have h := D.covariantTensorDerivative_commutator hA x a d ![d, b, c]
    change D.covariantTensorDerivative B x (Fin.cons a (Fin.cons d ![d, b, c])) -
      D.covariantTensorDerivative B x (Fin.cons d (Fin.cons a ![d, b, c])) =
      -D.covariantCurvatureAction A x a d ![d, b, c] at h
    rw [D.neg_covariantCurvatureAction_three] at h
    simp only [Matrix.Fin.cons_vecCons] at h
    rw [hDS]
    linarith only [h]
  dsimp only
  have htrace := D.covariantTensorDerivative_tensorLaplacian hD hT x a ![b, c]
  simp only [Matrix.Fin.cons_vecCons] at htrace
  rw [htrace]
  simp only [tensorLaplacian, iteratedCovariantTensorDerivative,
    Matrix.Fin.cons_vecCons, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun i _ => hpoint _)



lemma covariantTensorDerivative_tensorLaplacian_commutator_two
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    {T : CovariantTensorEvaluation n M 2} (hT : IsSmoothCovariantTensor T)
    (x : M) (a b c : TangentSpace (𝓡 n) x) :
    let e := g.orthonormalBasis x
    D.covariantTensorDerivative (D.tensorLaplacian T) x ![a, b, c] -
        D.tensorLaplacian (D.covariantTensorDerivative T) x ![a, b, c] =
      2 * (∑ i, ∑ j, D.curvatureTensor x a (e i) b (e j) *
        D.covariantTensorDerivative T x ![e i, e j, c]) +
      2 * (∑ i, ∑ j, D.curvatureTensor x a (e i) c (e j) *
        D.covariantTensorDerivative T x ![e i, b, e j]) -
      (∑ i, D.ricci x a (e i) * D.covariantTensorDerivative T x ![e i, b, c]) +
      (∑ j, (D.covariantTensorDerivative D.ricciEvaluation x ![e j, a, b] -
        D.covariantTensorDerivative D.ricciEvaluation x ![b, a, e j]) * T x ![e j, c]) +
      (∑ j, (D.covariantTensorDerivative D.ricciEvaluation x ![e j, a, c] -
        D.covariantTensorDerivative D.ricciEvaluation x ![c, a, e j]) * T x ![b, e j]) := by
  let e := g.orthonormalBasis x
  let A := D.covariantTensorDerivative T
  have hA := hD.2.2.1 _ _ hT
  have hleft (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      A x ![e i, D.curvature x a (e i) b, c] =
        ∑ j, D.curvatureTensor x a (e i) (e j) b * A x ![e i, e j, c] := by
    have h := D.tensor_curvature_slot_eq_sum hA x ![e i, b, c] 1 a (e i) b
    have hu (w : TangentSpace (𝓡 n) x) :
        Function.update ![e i, b, c] 1 w = ![e i, w, c] := by
      ext q
      fin_cases q <;> simp
    simpa only [hu] using h
  have hright (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      A x ![e i, b, D.curvature x a (e i) c] =
        ∑ j, D.curvatureTensor x a (e i) (e j) c * A x ![e i, b, e j] := by
    have h := D.tensor_curvature_slot_eq_sum hA x ![e i, b, c] 2 a (e i) c
    have hu (w : TangentSpace (𝓡 n) x) :
        Function.update ![e i, b, c] 2 w = ![e i, b, w] := by
      ext q
      fin_cases q <;> simp
    simpa only [hu] using h
  have hric := D.sum_curvature_cons_eq_ricci_mul hA x a ![b, c]
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
  have hraw := D.covariantTensorDerivative_tensorLaplacian_commutator_raw hD hT x a b c
  dsimp only at hraw ⊢
  simp_rw [D.covariantTensorDerivative_curvature_action_two hD hT] at hraw
  change _ = -∑ i, (A x ![D.curvature x a (e i) (e i), b, c] +
    A x ![e i, D.curvature x a (e i) b, c] + A x ![e i, b, D.curvature x a (e i) c] +
    ∑ j, (D.covariantTensorDerivative D.riemannEvaluation x ![e i, a, e i, e j, b] *
      T x ![e j, c] + D.curvatureTensor x a (e i) (e j) b * A x ![e i, e j, c] +
      D.covariantTensorDerivative D.riemannEvaluation x ![e i, a, e i, e j, c] *
      T x ![b, e j] + D.curvatureTensor x a (e i) (e j) c * A x ![e i, b, e j])) at hraw
  simp_rw [hleft, hright] at hraw
  simp only [Finset.sum_add_distrib] at hraw
  rw [hric, hdiv b (fun j => T x ![e j, c]), hdiv c (fun j => T x ![b, e j])] at hraw
  have hskew (i j : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)))
      (s : TangentSpace (𝓡 n) x) :
      D.curvatureTensor x a (e i) (e j) s = -D.curvatureTensor x a (e i) s (e j) :=
    (hD.2.2.2.1 x a (e i) (e j) s).1
  simp_rw [hskew] at hraw
  simp only [neg_mul, Finset.sum_neg_distrib, sub_mul, Finset.sum_sub_distrib] at hraw ⊢
  change _ = _ at hraw
  dsimp only [A, e] at hraw
  linarith only [hraw]

end PoincareConjecture.LeviCivitaData
