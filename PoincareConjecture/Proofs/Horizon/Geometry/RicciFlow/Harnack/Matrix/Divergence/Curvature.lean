import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Divergence
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Commutation.Contractions








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

lemma sum_covariantTensorDerivative_riemann_eq_hamiltonP
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (a b c : TangentSpace (𝓡 n) x) :
    (∑ i, D.covariantTensorDerivative D.riemannEvaluation x
      ![g.orthonormalBasis x i, g.orthonormalBasis x i, a, b, c]) =
      hamiltonP D x b c a := by
  simp_rw [D.covariantTensorDerivative_riemannEvaluation_skew_first hD x
    (g.orthonormalBasis x _) (g.orthonormalBasis x _) a b c]
  rw [Finset.sum_neg_distrib,
    D.sum_covariantTensorDerivative_riemannEvaluation_divergence hD]
  simp only [hamiltonP]
  rw [D.covariantTensorDerivative_ricciEvaluation_symm hD x c a b,
    D.covariantTensorDerivative_ricciEvaluation_symm hD x b a c]
  ring

lemma sum_secondCovariantTensorDerivative_riemann_divergence
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (s a b c : TangentSpace (𝓡 n) x) :
    (∑ i, D.covariantTensorDerivative
      (D.covariantTensorDerivative D.riemannEvaluation) x
      ![s, g.orthonormalBasis x i, g.orthonormalBasis x i, a, b, c]) =
      D.covariantTensorDerivative
        (fun y z => hamiltonP D y (z 0) (z 1) (z 2)) x ![s, b, c, a] := by
  let P : CovariantTensorEvaluation n M 3 := fun y z => hamiltonP D y (z 0) (z 1) (z 2)
  let σ : Equiv.Perm (Fin 3) := Equiv.ofBijective ![1, 2, 0] (by decide)
  have heq : g.tensorTrace (D.covariantTensorDerivative D.riemannEvaluation) =
      fun y z => P y (z ∘ σ) := by
    funext y z
    have hz : z = ![z 0, z 1, z 2] := by ext i; fin_cases i <;> rfl
    rw [hz]
    change (∑ i, D.covariantTensorDerivative D.riemannEvaluation y
      ![g.orthonormalBasis y i, g.orthonormalBasis y i, z 0, z 1, z 2]) = _
    exact sum_covariantTensorDerivative_riemann_eq_hamiltonP D hD y _ _ _
  have h := D.covariantTensorDerivative_tensorTrace (hD.2.2.1 _ _ hD.1) x s ![a, b, c]
  rw [heq, D.covariantTensorDerivative_reindex] at h
  simp only [Matrix.Fin.cons_vecCons] at h
  have hz : Fin.cons s (fun j : Fin 3 => (![s, a, b, c] (σ j).succ)) =
      ![s, b, c, a] := by ext i; fin_cases i <;> rfl
  change D.covariantTensorDerivative P x
    (Fin.cons s (fun j => (![s, a, b, c] (σ j).succ))) = _ at h
  rw [hz] at h
  exact h.symm

lemma sum_secondCovariantTensorDerivative_riemann_swap
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (s a b c : TangentSpace (𝓡 n) x) :
    let e := g.orthonormalBasis x
    (∑ i, D.covariantTensorDerivative
      (D.covariantTensorDerivative D.riemannEvaluation) x ![e i, s, e i, a, b, c]) =
      D.covariantTensorDerivative
        (fun y z => hamiltonP D y (z 0) (z 1) (z 2)) x ![s, b, c, a] +
      (∑ j, D.ricci x s (e j) * D.curvatureTensor x (e j) a b c) -
      (∑ i, ∑ j, D.curvatureTensor x (e i) s (e j) a *
        D.curvatureTensor x (e i) (e j) b c) -
      (∑ i, ∑ j, D.curvatureTensor x (e i) s (e j) b *
        D.curvatureTensor x (e i) a (e j) c) -
      (∑ i, ∑ j, D.curvatureTensor x (e i) s (e j) c *
        D.curvatureTensor x (e i) a b (e j)) := by
  let e := g.orthonormalBasis x
  have hcomm (i) := D.covariantTensorDerivative_commutator hD.1 x (e i) s ![e i, a, b, c]
  simp_rw [D.tensor_curvature_slot_eq_sum hD.1] at hcomm
  simp only [Matrix.Fin.cons_vecCons, Fin.sum_univ_four, LeviCivitaData.riemannEvaluation,
    Function.update_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    ↓reduceIte] at hcomm
  simp at hcomm
  have hsum := congrArg (fun f : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ =>
    ∑ i, f i) (funext hcomm)
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_add_distrib] at hsum
  have hfirst (p q r z : TangentSpace (𝓡 n) x) :
      D.curvatureTensor x p q r z = -D.curvatureTensor x q p r z := by
    rw [(hD.2.2.2.1 x p q r z).2.1, (hD.2.2.2.1 x r z p q).1,
      (hD.2.2.2.1 x r z q p).2.1]
  have htrace : (∑ i, ∑ j, D.curvatureTensor x (e i) s (e j) (e i) *
      D.curvatureTensor x (e j) a b c) =
      -(∑ j, D.ricci x s (e j) * D.curvatureTensor x (e j) a b c) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_mul]
    simp_rw [hfirst (e _) s]
    rw [Finset.sum_neg_distrib, neg_mul]
    rfl
  change (∑ i, D.covariantTensorDerivative
      (D.covariantTensorDerivative D.riemannEvaluation) x ![e i, s, e i, a, b, c]) = _
  rw [htrace] at hsum
  have hdiv := sum_secondCovariantTensorDerivative_riemann_divergence D hD x s a b c
  dsimp only [e] at hsum
  linarith only [hsum, hdiv]

lemma sum_secondCovariantTensorDerivative_riemann_swap_curvatureB
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (s a b c : TangentSpace (𝓡 n) x) :
    let e := g.orthonormalBasis x
    (∑ i, D.covariantTensorDerivative
      (D.covariantTensorDerivative D.riemannEvaluation) x ![e i, s, e i, a, b, c]) =
      D.covariantTensorDerivative
        (fun y z => hamiltonP D y (z 0) (z 1) (z 2)) x ![s, b, c, a] +
      (∑ j, D.ricci x s (e j) * D.curvatureTensor x (e j) a b c) +
      D.curvatureB x s a c b - D.curvatureB x s a b c +
      D.curvatureB x s c a b - D.curvatureB x s b a c := by
  let e := g.orthonormalBasis x
  have hfirst (p q r z : TangentSpace (𝓡 n) x) :
      D.curvatureTensor x p q r z = -D.curvatureTensor x q p r z := by
    rw [(hD.2.2.2.1 x p q r z).2.1, (hD.2.2.2.1 x r z p q).1,
      (hD.2.2.2.1 x r z q p).2.1]
  have hflip (p q r z : TangentSpace (𝓡 n) x) :
      D.curvatureTensor x p q r z = D.curvatureTensor x q p z r := by
    rw [hfirst p q r z, (hD.2.2.2.1 x q p r z).1, neg_neg]
  have hcyclic (i j) : D.curvatureTensor x (e i) (e j) b c =
      D.curvatureTensor x b (e i) c (e j) - D.curvatureTensor x c (e i) b (e j) := by
    have h := (hD.2.2.2.1 x (e i) (e j) b c).2.2.1
    rw [(hD.2.2.2.1 x (e j) b (e i) c).2.1,
      hflip (e i) c (e j) b, (hD.2.2.2.1 x b (e i) (e j) c).1] at h
    linarith only [h]
  have hA : (∑ i, ∑ j, D.curvatureTensor x (e i) s (e j) a *
        D.curvatureTensor x (e i) (e j) b c) =
      D.curvatureB x s a b c - D.curvatureB x s a c b := by
    simp_rw [hflip (e _) s, hcyclic, mul_sub]
    simp only [Finset.sum_sub_distrib]
    rfl
  have hB : (∑ i, ∑ j, D.curvatureTensor x (e i) s (e j) b *
        D.curvatureTensor x (e i) a (e j) c) = D.curvatureB x s b a c := by
    simp_rw [hflip (e _) s, hflip (e _) a]
    rfl
  have hC : (∑ i, ∑ j, D.curvatureTensor x (e i) s (e j) c *
        D.curvatureTensor x (e i) a b (e j)) = -D.curvatureB x s c a b := by
    simp_rw [hflip (e _) s, hfirst (e _) a, mul_neg]
    simp only [Finset.sum_neg_distrib]
    rfl
  have h := sum_secondCovariantTensorDerivative_riemann_swap D hD x s a b c
  dsimp only at h ⊢
  change (∑ i, D.covariantTensorDerivative
    (D.covariantTensorDerivative D.riemannEvaluation) x ![e i, s, e i, a, b, c]) = _ at h
  rw [hA, hB, hC] at h
  linarith only [h]

end Poincare.RicciFlow.Harnack
