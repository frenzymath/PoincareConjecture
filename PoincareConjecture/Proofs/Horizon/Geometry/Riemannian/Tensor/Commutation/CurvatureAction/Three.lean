import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Commutation.CurvatureAction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Commutation







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private lemma curvature_action_three_first_trace (D : LeviCivitaData g)
    {T : CovariantTensorEvaluation n M 3} (hT : IsSmoothCovariantTensor T) :
    let σ : Equiv.Perm (Fin 7) := Equiv.ofBijective ![2, 3, 0, 4, 1, 5, 6] (by decide)
    g.tensorTrace (fun y z => tensorProduct D.riemannEvaluation T y (z ∘ σ)) =
      fun y z => T y ![D.curvature y (z 0) (z 1) (z 2), z 3, z 4] := by
  dsimp only
  funext y z
  have h := D.tensor_curvature_slot_eq_sum hT y ![z 2, z 3, z 4] 0 (z 0) (z 1) (z 2)
  have hu (w : TangentSpace (𝓡 n) y) : Function.update ![z 2, z 3, z 4] 0 w =
      ![w, z 3, z 4] := by ext i; fin_cases i <;> simp
  simp only [hu] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  let σ : Equiv.Perm (Fin 7) := Equiv.ofBijective ![2, 3, 0, 4, 1, 5, 6] (by decide)
  have hz : (Fin.cons (g.orthonormalBasis y i)
      (Fin.cons (g.orthonormalBasis y i) z)) ∘ σ =
      ![z 0, z 1, g.orthonormalBasis y i, z 2, g.orthonormalBasis y i, z 3, z 4] := by
    ext j; fin_cases j <;> rfl
  change tensorProduct D.riemannEvaluation T y
    ((Fin.cons (g.orthonormalBasis y i) (Fin.cons (g.orthonormalBasis y i) z)) ∘ σ) = _
  rw [hz]
  change D.curvatureTensor y (z 0) (z 1) (g.orthonormalBasis y i) (z 2) *
    T y (fun j => ![z 0, z 1, g.orthonormalBasis y i, z 2,
      g.orthonormalBasis y i, z 3, z 4] (Fin.natAdd 4 j)) = _
  congr 1
  congr 1
  ext j; fin_cases j <;> rfl

lemma isSmoothCovariantTensor_curvature_action_three_first
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    {T : CovariantTensorEvaluation n M 3} (hT : IsSmoothCovariantTensor T) :
    IsSmoothCovariantTensor (fun y (z : Fin 5 → TangentSpace (𝓡 n) y) =>
      T y ![D.curvature y (z 0) (z 1) (z 2), z 3, z 4]) := by
  rw [← D.curvature_action_three_first_trace hT]
  exact ((isSmoothCovariantTensor_tensorProduct hD.1 hT).perm _).tensorTrace

lemma covariantTensorDerivative_curvature_action_three_first
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    {T : CovariantTensorEvaluation n M 3} (hT : IsSmoothCovariantTensor T)
    (x : M) (p a b c d e : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (fun y z =>
        T y ![D.curvature y (z 0) (z 1) (z 2), z 3, z 4]) x ![p, a, b, c, d, e] =
      ∑ i, (D.covariantTensorDerivative D.riemannEvaluation x
          ![p, a, b, g.orthonormalBasis x i, c] * T x ![g.orthonormalBasis x i, d, e] +
        D.curvatureTensor x a b (g.orthonormalBasis x i) c *
          D.covariantTensorDerivative T x ![p, g.orthonormalBasis x i, d, e]) := by
  let σ : Equiv.Perm (Fin 7) := Equiv.ofBijective ![2, 3, 0, 4, 1, 5, 6] (by decide)
  have hP := isSmoothCovariantTensor_tensorProduct hD.1 hT
  rw [← D.curvature_action_three_first_trace hT]
  have htrace := D.covariantTensorDerivative_tensorTrace (hP.perm σ) x p ![a, b, c, d, e]
  simp only [Matrix.Fin.cons_vecCons] at htrace
  rw [htrace]
  apply Finset.sum_congr rfl
  intro i _
  rw [D.covariantTensorDerivative_reindex]
  have heq : Fin.cons p (fun j : Fin 7 =>
      ![p, g.orthonormalBasis x i, g.orthonormalBasis x i, a, b, c, d, e]
        (σ j).succ) = ![p, a, b, g.orthonormalBasis x i, c, g.orthonormalBasis x i, d, e] := by
    ext j; fin_cases j <;> rfl
  change D.covariantTensorDerivative (tensorProduct D.riemannEvaluation T) x
    (Fin.cons p (fun j =>
      ![p, g.orthonormalBasis x i, g.orthonormalBasis x i, a, b, c, d, e] (σ j).succ)) = _
  rw [heq]
  have hp := D.covariantTensorDerivative_tensorProduct hD.1 hT x p
    ![a, b, g.orthonormalBasis x i, c, g.orthonormalBasis x i, d, e]
  simp only [Matrix.Fin.cons_vecCons] at hp
  rw [hp]
  congr 1
  · congr 1
    congr 1
    ext j; fin_cases j <;> rfl
  · congr 1
    congr 1
    ext j; fin_cases j <;> rfl

private lemma curvature_action_three_middle_perm (D : LeviCivitaData g)
    (T : CovariantTensorEvaluation n M 3) :
    (fun y (z : Fin 5 → TangentSpace (𝓡 n) y) =>
      T y ![z 2, D.curvature y (z 0) (z 1) (z 3), z 4]) =
      fun y z => (fun w : Fin 5 → TangentSpace (𝓡 n) y =>
        T y (![D.curvature y (w 0) (w 1) (w 2), w 3, w 4] ∘ Equiv.swap 0 1))
          (z ∘ Equiv.swap 2 3) := by
  funext y z
  congr 1
  ext i; fin_cases i <;> simp [Equiv.swap_apply_def]

lemma isSmoothCovariantTensor_curvature_action_three_middle
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    {T : CovariantTensorEvaluation n M 3} (hT : IsSmoothCovariantTensor T) :
    IsSmoothCovariantTensor (fun y (z : Fin 5 → TangentSpace (𝓡 n) y) =>
      T y ![z 2, D.curvature y (z 0) (z 1) (z 3), z 4]) := by
  rw [D.curvature_action_three_middle_perm T]
  exact (D.isSmoothCovariantTensor_curvature_action_three_first hD
    (hT.perm (Equiv.swap 0 1))).perm (Equiv.swap 2 3)

lemma covariantTensorDerivative_curvature_action_three_middle
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    {T : CovariantTensorEvaluation n M 3} (hT : IsSmoothCovariantTensor T)
    (x : M) (p a b c d e : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (fun y z =>
        T y ![z 2, D.curvature y (z 0) (z 1) (z 3), z 4]) x ![p, a, b, c, d, e] =
      ∑ i, (D.covariantTensorDerivative D.riemannEvaluation x
          ![p, a, b, g.orthonormalBasis x i, d] * T x ![c, g.orthonormalBasis x i, e] +
        D.curvatureTensor x a b (g.orthonormalBasis x i) d *
          D.covariantTensorDerivative T x ![p, c, g.orthonormalBasis x i, e]) := by
  let U : CovariantTensorEvaluation n M 3 := fun y z => T y (z ∘ Equiv.swap 0 1)
  let L : CovariantTensorEvaluation n M 5 := fun y z =>
    U y ![D.curvature y (z 0) (z 1) (z 2), z 3, z 4]
  rw [D.curvature_action_three_middle_perm T]
  change D.covariantTensorDerivative (fun y z => L y (z ∘ Equiv.swap 2 3)) x
    ![p, a, b, c, d, e] = _
  rw [D.covariantTensorDerivative_reindex]
  have hs : Fin.cons p (fun i : Fin 5 => ![p, a, b, c, d, e] ((Equiv.swap 2 3 i).succ)) =
      ![p, a, b, d, c, e] := by
    ext i; fin_cases i <;> simp [Equiv.swap_apply_def] <;> rfl
  change D.covariantTensorDerivative L x
    (Fin.cons p (fun i => ![p, a, b, c, d, e] ((Equiv.swap 2 3 i).succ))) = _
  rw [hs]
  change D.covariantTensorDerivative
    (fun y z => U y ![D.curvature y (z 0) (z 1) (z 2), z 3, z 4]) x ![p, a, b, d, c, e] = _
  rw [D.covariantTensorDerivative_curvature_action_three_first hD (hT.perm (Equiv.swap 0 1))]
  apply Finset.sum_congr rfl
  intro i _
  have hU : U x ![g.orthonormalBasis x i, c, e] = T x ![c, g.orthonormalBasis x i, e] := by
    change T x (![g.orthonormalBasis x i, c, e] ∘ Equiv.swap 0 1) = _
    congr 1
    ext j; fin_cases j <;> simp [Equiv.swap_apply_def]
  have hDU : D.covariantTensorDerivative U x ![p, g.orthonormalBasis x i, c, e] =
      D.covariantTensorDerivative T x ![p, c, g.orthonormalBasis x i, e] := by
    rw [show U = (fun y z => T y (z ∘ Equiv.swap 0 1)) from rfl,
      D.covariantTensorDerivative_reindex]
    congr 1
    ext j; fin_cases j <;> simp [Equiv.swap_apply_def] <;> rfl
  change _ * U x ![g.orthonormalBasis x i, c, e] +
    _ * D.covariantTensorDerivative U x ![p, g.orthonormalBasis x i, c, e] = _
  rw [hU, hDU]

private lemma curvature_action_three_last_perm (D : LeviCivitaData g)
    (T : CovariantTensorEvaluation n M 3) :
    (fun y (z : Fin 5 → TangentSpace (𝓡 n) y) =>
      T y ![z 2, z 3, D.curvature y (z 0) (z 1) (z 4)]) =
      fun y z => (fun w : Fin 5 → TangentSpace (𝓡 n) y =>
        T y (![D.curvature y (w 0) (w 1) (w 2), w 3, w 4] ∘ Equiv.swap 0 2))
          (z ∘ Equiv.swap 2 4) := by
  funext y z
  congr 1
  ext i; fin_cases i <;> simp [Equiv.swap_apply_def]

lemma isSmoothCovariantTensor_curvature_action_three_last
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    {T : CovariantTensorEvaluation n M 3} (hT : IsSmoothCovariantTensor T) :
    IsSmoothCovariantTensor (fun y (z : Fin 5 → TangentSpace (𝓡 n) y) =>
      T y ![z 2, z 3, D.curvature y (z 0) (z 1) (z 4)]) := by
  rw [D.curvature_action_three_last_perm T]
  exact (D.isSmoothCovariantTensor_curvature_action_three_first hD
    (hT.perm (Equiv.swap 0 2))).perm (Equiv.swap 2 4)

lemma covariantTensorDerivative_curvature_action_three_last
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    {T : CovariantTensorEvaluation n M 3} (hT : IsSmoothCovariantTensor T)
    (x : M) (p a b c d e : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (fun y z =>
        T y ![z 2, z 3, D.curvature y (z 0) (z 1) (z 4)]) x ![p, a, b, c, d, e] =
      ∑ i, (D.covariantTensorDerivative D.riemannEvaluation x
          ![p, a, b, g.orthonormalBasis x i, e] * T x ![c, d, g.orthonormalBasis x i] +
        D.curvatureTensor x a b (g.orthonormalBasis x i) e *
          D.covariantTensorDerivative T x ![p, c, d, g.orthonormalBasis x i]) := by
  let U : CovariantTensorEvaluation n M 3 := fun y z => T y (z ∘ Equiv.swap 0 2)
  let L : CovariantTensorEvaluation n M 5 := fun y z =>
    U y ![D.curvature y (z 0) (z 1) (z 2), z 3, z 4]
  rw [D.curvature_action_three_last_perm T]
  change D.covariantTensorDerivative (fun y z => L y (z ∘ Equiv.swap 2 4)) x
    ![p, a, b, c, d, e] = _
  rw [D.covariantTensorDerivative_reindex]
  have hs : Fin.cons p (fun i : Fin 5 => ![p, a, b, c, d, e] ((Equiv.swap 2 4 i).succ)) =
      ![p, a, b, e, d, c] := by
    ext i; fin_cases i <;> simp [Equiv.swap_apply_def] <;> rfl
  change D.covariantTensorDerivative L x
    (Fin.cons p (fun i => ![p, a, b, c, d, e] ((Equiv.swap 2 4 i).succ))) = _
  rw [hs]
  change D.covariantTensorDerivative
    (fun y z => U y ![D.curvature y (z 0) (z 1) (z 2), z 3, z 4]) x ![p, a, b, e, d, c] = _
  rw [D.covariantTensorDerivative_curvature_action_three_first hD (hT.perm (Equiv.swap 0 2))]
  apply Finset.sum_congr rfl
  intro i _
  have hU : U x ![g.orthonormalBasis x i, d, c] = T x ![c, d, g.orthonormalBasis x i] := by
    change T x (![g.orthonormalBasis x i, d, c] ∘ Equiv.swap 0 2) = _
    congr 1
    ext j; fin_cases j <;> simp [Equiv.swap_apply_def]
  have hDU : D.covariantTensorDerivative U x ![p, g.orthonormalBasis x i, d, c] =
      D.covariantTensorDerivative T x ![p, c, d, g.orthonormalBasis x i] := by
    rw [show U = (fun y z => T y (z ∘ Equiv.swap 0 2)) from rfl,
      D.covariantTensorDerivative_reindex]
    congr 1
    ext j; fin_cases j <;> simp [Equiv.swap_apply_def] <;> rfl
  change _ * U x ![g.orthonormalBasis x i, d, c] +
    _ * D.covariantTensorDerivative U x ![p, g.orthonormalBasis x i, d, c] = _
  rw [hU, hDU]

lemma covariantTensorDerivative_curvature_action_three
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    {T : CovariantTensorEvaluation n M 3} (hT : IsSmoothCovariantTensor T)
    (x : M) (p a b c d e : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (fun y z =>
        D.covariantCurvatureAction T y (z 0) (z 1) ![z 2, z 3, z 4]) x ![p, a, b, c, d, e] =
      ∑ i, (D.covariantTensorDerivative D.riemannEvaluation x
          ![p, a, b, g.orthonormalBasis x i, c] * T x ![g.orthonormalBasis x i, d, e] +
        D.curvatureTensor x a b (g.orthonormalBasis x i) c *
          D.covariantTensorDerivative T x ![p, g.orthonormalBasis x i, d, e] +
        D.covariantTensorDerivative D.riemannEvaluation x
          ![p, a, b, g.orthonormalBasis x i, d] * T x ![c, g.orthonormalBasis x i, e] +
        D.curvatureTensor x a b (g.orthonormalBasis x i) d *
          D.covariantTensorDerivative T x ![p, c, g.orthonormalBasis x i, e] +
        D.covariantTensorDerivative D.riemannEvaluation x
          ![p, a, b, g.orthonormalBasis x i, e] * T x ![c, d, g.orthonormalBasis x i] +
        D.curvatureTensor x a b (g.orthonormalBasis x i) e *
          D.covariantTensorDerivative T x ![p, c, d, g.orthonormalBasis x i]) := by
  simp_rw [D.covariantCurvatureAction_three]
  rw [D.covariantTensorDerivative_add
    ((D.isSmoothCovariantTensor_curvature_action_three_first hD hT).add
      (D.isSmoothCovariantTensor_curvature_action_three_middle hD hT))
    (D.isSmoothCovariantTensor_curvature_action_three_last hD hT)]
  rw [D.covariantTensorDerivative_add
    (D.isSmoothCovariantTensor_curvature_action_three_first hD hT)
    (D.isSmoothCovariantTensor_curvature_action_three_middle hD hT)]
  dsimp only
  rw [D.covariantTensorDerivative_curvature_action_three_first hD hT,
    D.covariantTensorDerivative_curvature_action_three_middle hD hT,
    D.covariantTensorDerivative_curvature_action_three_last hD hT]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

end PoincareConjecture.LeviCivitaData
