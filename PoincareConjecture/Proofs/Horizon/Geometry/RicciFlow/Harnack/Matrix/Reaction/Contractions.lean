import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Divergence.Curvature








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

lemma covariantTensorDerivative_hamiltonP_skew
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (p a b c : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (fun y z => hamiltonP D y (z 0) (z 1) (z 2)) x ![p, a, b, c] =
      -D.covariantTensorDerivative (fun y z => hamiltonP D y (z 0) (z 1) (z 2)) x ![p, b, a, c] := by
  rw [covariantTensorDerivative_hamiltonP D hD, covariantTensorDerivative_hamiltonP D hD]
  ring

lemma hamiltonP_quadratic_contraction
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (a b : TangentSpace (𝓡 n) x) :
    let e := g.orthonormalBasis x
    2 * (∑ i, ∑ j, hamiltonP D x a (e j) (e i) * hamiltonP D x (e i) (e j) b) +
      2 * (∑ i, ∑ j, hamiltonP D x b (e j) (e i) * hamiltonP D x (e i) a (e j)) =
      (∑ i, ∑ j, hamiltonP D x (e i) (e j) a * hamiltonP D x (e i) (e j) b) -
        2 * (∑ i, ∑ j, hamiltonP D x a (e i) (e j) * hamiltonP D x b (e j) (e i)) := by
  let e := g.orthonormalBasis x
  have hswap : (∑ i, ∑ j, hamiltonP D x a (e j) (e i) * hamiltonP D x (e i) (e j) b) =
      -(∑ i, ∑ j, hamiltonP D x a (e i) (e j) * hamiltonP D x (e i) (e j) b) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hamiltonP_skew D x (e j) (e i) b]
    ring
  have hcyclic (i j) : hamiltonP D x (e i) (e j) a =
      hamiltonP D x a (e j) (e i) - hamiltonP D x a (e i) (e j) := by
    have h := hamiltonP_cyclic D hD x a (e j) (e i)
    rw [hamiltonP_skew D x (e j) (e i) a, hamiltonP_skew D x (e i) a (e j)] at h
    linarith only [h]
  have hB : (∑ i, ∑ j, hamiltonP D x b (e j) (e i) * hamiltonP D x (e i) a (e j)) =
      -(∑ i, ∑ j, hamiltonP D x a (e i) (e j) * hamiltonP D x b (e j) (e i)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hamiltonP_skew D x (e i) a (e j)]
    ring
  change 2 * (∑ i, ∑ j, hamiltonP D x a (e j) (e i) * hamiltonP D x (e i) (e j) b) + _ = _
  rw [hB]
  dsimp only [e] at hcyclic hswap ⊢
  simp_rw [hcyclic, sub_mul]
  simp only [Finset.sum_sub_distrib]
  linarith only [hswap]

lemma hamiltonP_curvature_gradient_contraction
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (a b : TangentSpace (𝓡 n) x) :
    let e := g.orthonormalBasis x
    (∑ k, ∑ i, ∑ j, D.covariantTensorDerivative D.riemannEvaluation x ![e k, a, e i, b, e j] *
      hamiltonP D x (e k) (e i) (e j)) -
    (∑ k, ∑ i, ∑ j, D.covariantTensorDerivative D.ricciEvaluation x ![e k, e i, e j] *
      D.covariantTensorDerivative D.riemannEvaluation x ![e i, e k, a, b, e j]) =
    ∑ k, ∑ i, ∑ j, D.covariantTensorDerivative D.riemannEvaluation x ![e k, a, e i, b, e j] *
      D.covariantTensorDerivative D.ricciEvaluation x ![e k, e i, e j] := by
  let e := g.orthonormalBasis x
  have hswap : (∑ k, ∑ i, ∑ j, D.covariantTensorDerivative D.ricciEvaluation x ![e k, e i, e j] *
      D.covariantTensorDerivative D.riemannEvaluation x ![e i, e k, a, b, e j]) =
      -(∑ k, ∑ i, ∑ j, D.covariantTensorDerivative D.riemannEvaluation x ![e k, a, e i, b, e j] *
        D.covariantTensorDerivative D.ricciEvaluation x ![e i, e k, e j]) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [D.covariantTensorDerivative_riemannEvaluation_skew_first hD x (e k) (e i) a b (e j)]
    ring
  change (∑ k, ∑ i, ∑ j, D.covariantTensorDerivative D.riemannEvaluation x ![e k, a, e i, b, e j] *
    hamiltonP D x (e k) (e i) (e j)) - _ = _
  rw [hswap]
  simp only [hamiltonP, mul_sub, Finset.sum_sub_distrib]
  ring

lemma curvature_skew_contraction
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (a : TangentSpace (𝓡 n) x)
    (Z : TangentSpace (𝓡 n) x → TangentSpace (𝓡 n) x → TangentSpace (𝓡 n) x → ℝ) :
    let e := g.orthonormalBasis x
    (∑ k, ∑ i, ∑ j, D.curvatureTensor x (e k) (e i) a (e j) * Z (e k) (e i) (e j)) +
      (∑ k, ∑ i, ∑ j, D.curvatureTensor x (e k) (e i) a (e j) * Z (e i) (e k) (e j)) = 0 := by
  let e := g.orthonormalBasis x
  have hswap : (∑ k, ∑ i, ∑ j, D.curvatureTensor x (e k) (e i) a (e j) * Z (e i) (e k) (e j)) =
      -(∑ k, ∑ i, ∑ j, D.curvatureTensor x (e k) (e i) a (e j) * Z (e k) (e i) (e j)) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [(hD.2.2.2.1 x (e i) (e k) a (e j)).2.1,
      (hD.2.2.2.1 x a (e j) (e i) (e k)).1,
      (hD.2.2.2.1 x a (e j) (e k) (e i)).2.1]
    ring
  dsimp only [e] at hswap
  dsimp only
  rw [hswap]
  ring

lemma curvature_divergence_contraction
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (a : TangentSpace (𝓡 n) x)
    (Z : TangentSpace (𝓡 n) x → TangentSpace (𝓡 n) x → ℝ) :
    let e := g.orthonormalBasis x
    (∑ k, ∑ i, ∑ j, D.covariantTensorDerivative D.riemannEvaluation x
      ![e k, e k, e i, a, e j] * Z (e i) (e j)) =
      ∑ i, ∑ j, hamiltonP D x a (e j) (e i) * Z (e i) (e j) := by
  dsimp only
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_mul, sum_covariantTensorDerivative_riemann_eq_hamiltonP D hD]

lemma ricci_second_curvature_contraction
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (a b : TangentSpace (𝓡 n) x) :
    let e := g.orthonormalBasis x
    let P : CovariantTensorEvaluation n M 3 := fun y z => hamiltonP D y (z 0) (z 1) (z 2)
    (∑ k, ∑ i, ∑ j, D.ricci x (e i) (e j) * D.covariantTensorDerivative
      (D.covariantTensorDerivative D.riemannEvaluation) x ![e k, e i, e k, a, b, e j]) =
      -(∑ i, ∑ j, D.ricci x (e i) (e j) * D.covariantTensorDerivative P x ![e i, e j, b, a]) -
      (∑ i, ∑ j, ∑ k, D.ricci x (e i) (e j) * D.ricci x (e i) (e k) *
        D.curvatureTensor x a (e k) b (e j)) +
      (∑ i, ∑ j, D.ricci x (e i) (e j) *
        (D.curvatureB x (e i) a (e j) b - D.curvatureB x (e i) a b (e j) +
          D.curvatureB x (e i) (e j) a b - D.curvatureB x (e i) b a (e j))) := by
  let e := g.orthonormalBasis x
  have hterm (i j) : (∑ k, D.ricci x (e i) (e j) * D.covariantTensorDerivative
      (D.covariantTensorDerivative D.riemannEvaluation) x ![e k, e i, e k, a, b, e j]) =
      -(D.ricci x (e i) (e j) * D.covariantTensorDerivative
        (fun y z => hamiltonP D y (z 0) (z 1) (z 2)) x ![e i, e j, b, a]) -
      (∑ k, D.ricci x (e i) (e j) * D.ricci x (e i) (e k) * D.curvatureTensor x a (e k) b (e j)) +
      D.ricci x (e i) (e j) * (D.curvatureB x (e i) a (e j) b - D.curvatureB x (e i) a b (e j) +
        D.curvatureB x (e i) (e j) a b - D.curvatureB x (e i) b a (e j)) := by
    rw [← Finset.mul_sum, sum_secondCovariantTensorDerivative_riemann_swap_curvatureB D hD]
    rw [covariantTensorDerivative_hamiltonP_skew D hD x (e i) b (e j) a]
    have hcurv (k) : D.curvatureTensor x (e k) a b (e j) = -D.curvatureTensor x a (e k) b (e j) := by
      rw [(hD.2.2.2.1 x (e k) a b (e j)).2.1,
        (hD.2.2.2.1 x b (e j) (e k) a).1,
        (hD.2.2.2.1 x b (e j) a (e k)).2.1]
    dsimp only [e] at hcurv ⊢
    simp_rw [hcurv, mul_neg]
    simp only [Finset.sum_neg_distrib, mul_assoc, ← Finset.mul_sum]
    ring
  dsimp only
  rw [Finset.sum_comm]
  have horder (i) : (∑ k, ∑ j, D.ricci x (e i) (e j) * D.covariantTensorDerivative
      (D.covariantTensorDerivative D.riemannEvaluation) x ![e k, e i, e k, a, b, e j]) =
      ∑ j, ∑ k, D.ricci x (e i) (e j) * D.covariantTensorDerivative
      (D.covariantTensorDerivative D.riemannEvaluation) x ![e k, e i, e k, a, b, e j] := Finset.sum_comm
  dsimp only [e] at horder hterm
  simp_rw [horder, hterm]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]

end Poincare.RicciFlow.Harnack
