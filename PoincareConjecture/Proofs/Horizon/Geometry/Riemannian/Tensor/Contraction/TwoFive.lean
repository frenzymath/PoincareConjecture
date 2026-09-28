import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Trace.Double
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.ProductDerivative


set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

private noncomputable def twoFiveContractionPerm : Equiv.Perm (Fin 7) :=
  Equiv.ofBijective ![0, 2, 1, 4, 5, 6, 3] (by decide)

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private lemma two_five_eq_double_trace
    (A : CovariantTensorEvaluation n M 2) (T : CovariantTensorEvaluation n M 5) :
    (fun y (z : Fin 3 → TangentSpace (𝓡 n) y) =>
      ∑ i, ∑ j, A y ![g.orthonormalBasis y i, g.orthonormalBasis y j] *
        T y ![g.orthonormalBasis y i, z 0, z 1, z 2, g.orthonormalBasis y j]) =
    g.tensorTrace (g.tensorTrace (fun y z => tensorProduct A T y
      (z ∘ (twoFiveContractionPerm)))) := by
  funext y z
  symm
  let e := g.orthonormalBasis y
  let σ : Equiv.Perm (Fin 7) := twoFiveContractionPerm
  simp only [RiemannianMetric.tensorTrace]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hz : (Fin.cons (e i) (Fin.cons (e i) (Fin.cons (e j) (Fin.cons (e j) z))) :
      Fin 7 → TangentSpace (𝓡 n) y) ∘ σ =
      ![e i, e j, e i, z 0, z 1, z 2, e j] := by ext q; fin_cases q <;> rfl
  change tensorProduct A T y
    ((Fin.cons (e i) (Fin.cons (e i) (Fin.cons (e j) (Fin.cons (e j) z))) :
      Fin 7 → TangentSpace (𝓡 n) y) ∘ σ) = _
  rw [hz]
  rw [tensorProduct_apply]
  have hA : (fun q : Fin 2 => ![e i, e j, e i, z 0, z 1, z 2, e j] (Fin.castAdd 5 q)) =
      ![e i, e j] := by ext q; fin_cases q <;> rfl
  have hT : (fun q : Fin 5 => ![e i, e j, e i, z 0, z 1, z 2, e j] (Fin.natAdd 2 q)) =
      ![e i, z 0, z 1, z 2, e j] := by ext q; fin_cases q <;> rfl
  rw [hA, hT]

lemma isSmoothCovariantTensor_two_five_contraction
    (_D : LeviCivitaData g) {A : CovariantTensorEvaluation n M 2}
    {T : CovariantTensorEvaluation n M 5} (hA : IsSmoothCovariantTensor A)
    (hT : IsSmoothCovariantTensor T) :
    IsSmoothCovariantTensor (fun y (z : Fin 3 → TangentSpace (𝓡 n) y) =>
      ∑ i, ∑ j, A y ![g.orthonormalBasis y i, g.orthonormalBasis y j] *
        T y ![g.orthonormalBasis y i, z 0, z 1, z 2, g.orthonormalBasis y j]) := by
  rw [two_five_eq_double_trace (g := g) A T]
  exact ((isSmoothCovariantTensor_tensorProduct hA hT).perm _).tensorTrace.tensorTrace

private lemma derivative_product_two_five
    (D : LeviCivitaData g) {A : CovariantTensorEvaluation n M 2}
    {T : CovariantTensorEvaluation n M 5} (hA : IsSmoothCovariantTensor A)
    (hT : IsSmoothCovariantTensor T) (x : M) (p q r a b c : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (tensorProduct A T) x ![p, q, r, q, a, b, c, r] =
      D.covariantTensorDerivative A x ![p, q, r] * T x ![q, a, b, c, r] +
      A x ![q, r] * D.covariantTensorDerivative T x ![p, q, a, b, c, r] := by
  have hp := D.covariantTensorDerivative_tensorProduct hA hT x p ![q, r, q, a, b, c, r]
  have hv₁ : (fun j : Fin 2 => ![q, r, q, a, b, c, r] (Fin.castAdd 5 j)) =
      ![q, r] := by ext j; fin_cases j <;> rfl
  have hv₂ : (fun j : Fin 5 => ![q, r, q, a, b, c, r] (Fin.natAdd 2 j)) =
      ![q, a, b, c, r] := by ext j; fin_cases j <;> rfl
  simpa only [hv₁, hv₂, Matrix.Fin.cons_vecCons] using hp

private lemma two_five_permutation_cons {V : Type*} (p q r a b c : V) :
    Fin.cons (![p, q, q, r, r, a, b, c] 0)
      (fun j : Fin 7 => ![p, q, q, r, r, a, b, c] (twoFiveContractionPerm j).succ) =
      ![p, q, r, q, a, b, c, r] := by
  ext j

  fin_cases j <;> simp [twoFiveContractionPerm, Fin.cons] <;> rfl

private lemma derivative_two_five_permutation
    (D : LeviCivitaData g) (U : CovariantTensorEvaluation n M 7)
    (x : M) (p q r a b c : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (fun y z => U y (z ∘ twoFiveContractionPerm)) x
      ![p, q, q, r, r, a, b, c] =
      D.covariantTensorDerivative U x ![p, q, r, q, a, b, c, r] := by
  exact (D.covariantTensorDerivative_reindex U twoFiveContractionPerm x
    ![p, q, q, r, r, a, b, c]).trans
      (congrArg (D.covariantTensorDerivative U x) (two_five_permutation_cons p q r a b c))

private lemma derivative_permuted_product_two_five
    (D : LeviCivitaData g) {A : CovariantTensorEvaluation n M 2}
    {T : CovariantTensorEvaluation n M 5} (hA : IsSmoothCovariantTensor A)
    (hT : IsSmoothCovariantTensor T) (x : M) (p q r a b c : TangentSpace (𝓡 n) x) :
    let σ : Equiv.Perm (Fin 7) := twoFiveContractionPerm
    D.covariantTensorDerivative (fun y z => tensorProduct A T y (z ∘ σ)) x
      ![p, q, q, r, r, a, b, c] =
      D.covariantTensorDerivative A x ![p, q, r] * T x ![q, a, b, c, r] +
      A x ![q, r] * D.covariantTensorDerivative T x ![p, q, a, b, c, r] := by
  exact (D.derivative_two_five_permutation (tensorProduct A T) x p q r a b c).trans
    (D.derivative_product_two_five hA hT x p q r a b c)

lemma covariantTensorDerivative_two_five_contraction
    (D : LeviCivitaData g) {A : CovariantTensorEvaluation n M 2}
    {T : CovariantTensorEvaluation n M 5} (hA : IsSmoothCovariantTensor A)
    (hT : IsSmoothCovariantTensor T)
    (x : M) (p a b c : TangentSpace (𝓡 n) x) :
    let e := g.orthonormalBasis x
    D.covariantTensorDerivative (fun y z =>
      ∑ i, ∑ j, A y ![g.orthonormalBasis y i, g.orthonormalBasis y j] *
        T y ![g.orthonormalBasis y i, z 0, z 1, z 2, g.orthonormalBasis y j]) x ![p, a, b, c] =
      ∑ i, ∑ j, (D.covariantTensorDerivative A x ![p, e i, e j] *
        T x ![e i, a, b, c, e j] + A x ![e i, e j] *
        D.covariantTensorDerivative T x ![p, e i, a, b, c, e j]) := by
  let σ : Equiv.Perm (Fin 7) := twoFiveContractionPerm
  let S := fun y z => tensorProduct A T y (z ∘ σ)
  have hS : IsSmoothCovariantTensor S := (isSmoothCovariantTensor_tensorProduct hA hT).perm σ
  rw [two_five_eq_double_trace (g := g) A T]
  have h := D.covariantTensorDerivative_tensorTrace_tensorTrace hS x p ![a, b, c]
  simp only [Matrix.Fin.cons_vecCons] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact D.derivative_permuted_product_two_five hA hT x p
    (g.orthonormalBasis x i) (g.orthonormalBasis x j) a b c

end PoincareConjecture.LeviCivitaData
