import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Tensor.RicciAction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Commutation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private noncomputable def ricciSlot (D : LeviCivitaData g)
    (T : CovariantTensorEvaluation n M 3) (r : Fin 3) : CovariantTensorEvaluation n M 3 :=
  fun y z => ∑ i, D.ricci y (z r) (g.orthonormalBasis y i) *
    T y (Function.update z r (g.orthonormalBasis y i))

private lemma ricciSlot_first_trace (D : LeviCivitaData g)
    (T : CovariantTensorEvaluation n M 3) :
    let σ : Equiv.Perm (Fin 5) := Equiv.ofBijective ![2, 0, 1, 3, 4] (by decide)
    g.tensorTrace (fun y z => tensorProduct D.ricciEvaluation T y (z ∘ σ)) =
      ricciSlot D T 0 := by
  funext y z
  apply Finset.sum_congr rfl
  intro i _
  change D.ricci y (z 0) (g.orthonormalBasis y i) * _ = _
  congr 1
  congr 1
  ext j; fin_cases j <;> simp <;> rfl

private lemma smooth_ricciSlot_first (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    {T : CovariantTensorEvaluation n M 3} (hT : IsSmoothCovariantTensor T) :
    IsSmoothCovariantTensor (ricciSlot D T 0) := by
  rw [← ricciSlot_first_trace]
  exact ((isSmoothCovariantTensor_tensorProduct hD.2.1 hT).perm _).tensorTrace

private lemma derivative_ricciSlot_first (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    {T : CovariantTensorEvaluation n M 3} (hT : IsSmoothCovariantTensor T)
    (x : M) (a : TangentSpace (𝓡 n) x) (v : Fin 3 → TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (ricciSlot D T 0) x (Fin.cons a v) =
      ∑ i, (D.covariantTensorDerivative D.ricciEvaluation x ![a, v 0, g.orthonormalBasis x i] *
          T x (Function.update v 0 (g.orthonormalBasis x i)) +
        D.ricci x (v 0) (g.orthonormalBasis x i) *
          D.covariantTensorDerivative T x (Fin.cons a (Function.update v 0 (g.orthonormalBasis x i)))) := by
  let σ : Equiv.Perm (Fin 5) := Equiv.ofBijective ![2, 0, 1, 3, 4] (by decide)
  have hP := isSmoothCovariantTensor_tensorProduct hD.2.1 hT
  rw [← ricciSlot_first_trace]
  rw [D.covariantTensorDerivative_tensorTrace (hP.perm σ)]
  apply Finset.sum_congr rfl
  intro i _
  rw [D.covariantTensorDerivative_reindex]
  have heq : Fin.cons a (fun j : Fin 5 =>
      (Fin.cons (g.orthonormalBasis x i) (Fin.cons (g.orthonormalBasis x i) v) :
        Fin 5 → TangentSpace (𝓡 n) x) (σ j)) =
      (Fin.cons a ![v 0, g.orthonormalBasis x i, g.orthonormalBasis x i, v 1, v 2] :
        Fin 6 → TangentSpace (𝓡 n) x) := by
    ext j; fin_cases j <;> rfl
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [heq, D.covariantTensorDerivative_tensorProduct hD.2.1 hT]
  have hu : (fun j : Fin 3 =>
      ![v 0, g.orthonormalBasis x i, g.orthonormalBasis x i, v 1, v 2] (Fin.natAdd 2 j)) =
      Function.update v 0 (g.orthonormalBasis x i) := by
    ext j; fin_cases j <;> simp
  have hv : (fun j : Fin 2 =>
      ![v 0, g.orthonormalBasis x i, g.orthonormalBasis x i, v 1, v 2] (Fin.castAdd 3 j)) =
      ![v 0, g.orthonormalBasis x i] := by
    ext j; fin_cases j <;> rfl
  simp only [hu, hv, Matrix.Fin.cons_vecCons]
  rfl

private lemma ricciSlot_perm (D : LeviCivitaData g)
    (T : CovariantTensorEvaluation n M 3) (r : Fin 3) :
    ricciSlot D T r = fun y z =>
      ricciSlot D (fun y w => T y (w ∘ Equiv.swap 0 r)) 0 y (z ∘ Equiv.swap 0 r) := by
  funext y z
  apply Finset.sum_congr rfl
  intro i _
  simp only [Function.comp_apply, Equiv.swap_apply_left]
  congr 1
  congr 1
  ext j
  fin_cases r <;> fin_cases j <;> simp [Equiv.swap_apply_def]

private lemma smooth_ricciSlot (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    {T : CovariantTensorEvaluation n M 3} (hT : IsSmoothCovariantTensor T) (r : Fin 3) :
    IsSmoothCovariantTensor (ricciSlot D T r) := by
  rw [ricciSlot_perm]
  exact (smooth_ricciSlot_first D hD (hT.perm (Equiv.swap 0 r))).perm (Equiv.swap 0 r)

private lemma derivative_ricciSlot (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    {T : CovariantTensorEvaluation n M 3} (hT : IsSmoothCovariantTensor T)
    (x : M) (a : TangentSpace (𝓡 n) x) (v : Fin 3 → TangentSpace (𝓡 n) x) (r : Fin 3) :
    D.covariantTensorDerivative (ricciSlot D T r) x (Fin.cons a v) =
      ∑ i, (D.covariantTensorDerivative D.ricciEvaluation x ![a, v r, g.orthonormalBasis x i] *
          T x (Function.update v r (g.orthonormalBasis x i)) +
        D.ricci x (v r) (g.orthonormalBasis x i) *
          D.covariantTensorDerivative T x (Fin.cons a (Function.update v r (g.orthonormalBasis x i)))) := by
  rw [ricciSlot_perm, D.covariantTensorDerivative_reindex]
  change D.covariantTensorDerivative (ricciSlot D
    (fun y w => T y (w ∘ Equiv.swap 0 r)) 0) x (Fin.cons a (v ∘ Equiv.swap 0 r)) = _
  rw [derivative_ricciSlot_first D hD (hT.perm (Equiv.swap 0 r))]
  apply Finset.sum_congr rfl
  intro i _
  rw [D.covariantTensorDerivative_reindex]
  have hu (w : TangentSpace (𝓡 n) x) :
      Function.update (v ∘ Equiv.swap 0 r) 0 w ∘ Equiv.swap 0 r = Function.update v r w := by
    ext j
    fin_cases r <;> fin_cases j <;> simp [Equiv.swap_apply_def]
  simp only [Function.comp_apply, Equiv.swap_apply_left, Fin.cons_zero, Fin.cons_succ]
  change _ * T x (Function.update (v ∘ Equiv.swap 0 r) 0 (g.orthonormalBasis x i) ∘ Equiv.swap 0 r) +
    _ * D.covariantTensorDerivative T x (Fin.cons a
      (Function.update (v ∘ Equiv.swap 0 r) 0 (g.orthonormalBasis x i) ∘ Equiv.swap 0 r)) = _
  rw [hu]

lemma isSmoothCovariantTensor_ricciTensorAction_three
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    {T : CovariantTensorEvaluation n M 3} (hT : IsSmoothCovariantTensor T) :
    IsSmoothCovariantTensor (D.ricciTensorAction T) := by
  have heq : D.ricciTensorAction T = fun y z =>
      ricciSlot D T 0 y z + ricciSlot D T 1 y z + ricciSlot D T 2 y z := by
    funext y z
    exact Fin.sum_univ_three _
  rw [heq]
  exact ((smooth_ricciSlot D hD hT 0).add (smooth_ricciSlot D hD hT 1)).add
    (smooth_ricciSlot D hD hT 2)

lemma covariantTensorDerivative_ricciTensorAction_three
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    {T : CovariantTensorEvaluation n M 3} (hT : IsSmoothCovariantTensor T)
    (x : M) (a : TangentSpace (𝓡 n) x) (v : Fin 3 → TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (D.ricciTensorAction T) x (Fin.cons a v) =
      ∑ r : Fin 3, ∑ i, (D.covariantTensorDerivative D.ricciEvaluation x ![a, v r, g.orthonormalBasis x i] *
          T x (Function.update v r (g.orthonormalBasis x i)) +
        D.ricci x (v r) (g.orthonormalBasis x i) *
          D.covariantTensorDerivative T x (Fin.cons a (Function.update v r (g.orthonormalBasis x i)))) := by
  have heq : D.ricciTensorAction T = fun y z =>
      ricciSlot D T 0 y z + ricciSlot D T 1 y z + ricciSlot D T 2 y z := by
    funext y z
    exact Fin.sum_univ_three _
  rw [heq, D.covariantTensorDerivative_add
    ((smooth_ricciSlot D hD hT 0).add (smooth_ricciSlot D hD hT 1)) (smooth_ricciSlot D hD hT 2),
    D.covariantTensorDerivative_add (smooth_ricciSlot D hD hT 0) (smooth_ricciSlot D hD hT 1)]
  simp only [derivative_ricciSlot D hD hT, Fin.sum_univ_three]

end PoincareConjecture.LeviCivitaData
