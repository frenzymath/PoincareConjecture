import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.ProductDerivative
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.TraceRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Linearity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Algebra

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

lemma tensor_curvature_slot_eq_sum (D : LeviCivitaData g)
    {k : ℕ} {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T)
    (x : M) (v : Fin k → TangentSpace (𝓡 n) x) (i : Fin k)
    (a b c : TangentSpace (𝓡 n) x) :
    T x (Function.update v i (D.curvature x a b c)) =
      ∑ j, D.curvatureTensor x a b (g.orthonormalBasis x j) c *
        T x (Function.update v i (g.orthonormalBasis x j)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨A, hA⟩ := hT.1 x
  let L := A.toLinearMap v i
  have hL (w : TangentSpace (𝓡 n) x) : L w = T x (Function.update v i w) :=
    (hA _).symm
  have h := congrArg L ((g.orthonormalBasis x).sum_repr' (D.curvature x a b c))
  simp only [map_sum, map_smul, smul_eq_mul] at h
  simp only [hL] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_comm]
  rfl

private lemma curvature_action_left_trace (D : LeviCivitaData g)
    {T : CovariantTensorEvaluation n M 2} (hT : IsSmoothCovariantTensor T) :
    let σ : Equiv.Perm (Fin 6) := Equiv.ofBijective ![2, 3, 0, 4, 1, 5] (by decide)
    g.tensorTrace (fun y z => tensorProduct D.riemannEvaluation T y (z ∘ σ)) =
      fun y z => T y ![D.curvature y (z 0) (z 1) (z 2), z 3] := by
  dsimp only
  funext y z
  have h := D.tensor_curvature_slot_eq_sum hT y ![z 2, z 3] 0 (z 0) (z 1) (z 2)
  have hu (w : TangentSpace (𝓡 n) y) : Function.update ![z 2, z 3] 0 w = ![w, z 3] := by
    ext i
    fin_cases i <;> simp
  simp only [hu] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  let σ : Equiv.Perm (Fin 6) := Equiv.ofBijective ![2, 3, 0, 4, 1, 5] (by decide)
  have hz : (Fin.cons (g.orthonormalBasis y i)
      (Fin.cons (g.orthonormalBasis y i) z)) ∘ σ =
      ![z 0, z 1, g.orthonormalBasis y i, z 2, g.orthonormalBasis y i, z 3] := by
    ext j
    fin_cases j <;> rfl
  change tensorProduct D.riemannEvaluation T y
    ((Fin.cons (g.orthonormalBasis y i) (Fin.cons (g.orthonormalBasis y i) z)) ∘ σ) = _
  rw [hz]
  change D.curvatureTensor y (z 0) (z 1) (g.orthonormalBasis y i) (z 2) *
    T y (fun j => ![z 0, z 1, g.orthonormalBasis y i, z 2,
      g.orthonormalBasis y i, z 3] (Fin.natAdd 4 j)) = _
  congr 1
  congr 1
  ext j
  fin_cases j <;> rfl

lemma covariantTensorDerivative_curvature_action_left
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    {T : CovariantTensorEvaluation n M 2} (hT : IsSmoothCovariantTensor T)
    (x : M) (p a b c d : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (fun y z =>
        T y ![D.curvature y (z 0) (z 1) (z 2), z 3]) x ![p, a, b, c, d] =
      ∑ i, (D.covariantTensorDerivative D.riemannEvaluation x
          ![p, a, b, g.orthonormalBasis x i, c] * T x ![g.orthonormalBasis x i, d] +
        D.curvatureTensor x a b (g.orthonormalBasis x i) c *
          D.covariantTensorDerivative T x ![p, g.orthonormalBasis x i, d]) := by
  let σ : Equiv.Perm (Fin 6) := Equiv.ofBijective ![2, 3, 0, 4, 1, 5] (by decide)
  have hP := isSmoothCovariantTensor_tensorProduct hD.1 hT
  rw [← D.curvature_action_left_trace hT]
  have htrace := D.covariantTensorDerivative_tensorTrace (hP.perm σ) x p ![a, b, c, d]
  simp only [Matrix.Fin.cons_vecCons] at htrace
  rw [htrace]
  apply Finset.sum_congr rfl
  intro i _
  rw [D.covariantTensorDerivative_reindex]
  have heq : Fin.cons p (fun j : Fin 6 =>
      ![p, g.orthonormalBasis x i, g.orthonormalBasis x i, a, b, c, d]
        (σ j).succ) = ![p, a, b, g.orthonormalBasis x i, c, g.orthonormalBasis x i, d] := by
    ext j
    fin_cases j <;> rfl
  change D.covariantTensorDerivative (tensorProduct D.riemannEvaluation T) x
      (Fin.cons p (fun j =>
        ![p, g.orthonormalBasis x i, g.orthonormalBasis x i, a, b, c, d] (σ j).succ)) = _
  rw [heq]
  have hp := D.covariantTensorDerivative_tensorProduct hD.1 hT x p
    ![a, b, g.orthonormalBasis x i, c, g.orthonormalBasis x i, d]
  simp only [Matrix.Fin.cons_vecCons] at hp
  rw [hp]
  congr 1
  · congr 1
    congr 1
    ext j
    fin_cases j <;> rfl
  · congr 1
    congr 1
    ext j
    fin_cases j <;> rfl

private lemma isSmooth_curvature_action_left
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    {T : CovariantTensorEvaluation n M 2} (hT : IsSmoothCovariantTensor T) :
    IsSmoothCovariantTensor (fun y (z : Fin 4 → TangentSpace (𝓡 n) y) =>
      T y ![D.curvature y (z 0) (z 1) (z 2), z 3]) := by
  rw [← D.curvature_action_left_trace hT]
  exact ((isSmoothCovariantTensor_tensorProduct hD.1 hT).perm _).tensorTrace

private lemma curvature_action_right_perm (D : LeviCivitaData g)
    (T : CovariantTensorEvaluation n M 2) :
    (fun y (z : Fin 4 → TangentSpace (𝓡 n) y) =>
      T y ![z 2, D.curvature y (z 0) (z 1) (z 3)]) =
      fun y z => (fun (w : Fin 4 → TangentSpace (𝓡 n) y) =>
        (fun v => T y (v ∘ Equiv.swap 0 1))
          ![D.curvature y (w 0) (w 1) (w 2), w 3]) (z ∘ Equiv.swap 2 3) := by
  funext y z
  congr 1
  ext i
  fin_cases i <;> simp [Equiv.swap_apply_def]

lemma covariantTensorDerivative_curvature_action_right
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    {T : CovariantTensorEvaluation n M 2} (hT : IsSmoothCovariantTensor T)
    (x : M) (p a b c d : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (fun y z =>
        T y ![z 2, D.curvature y (z 0) (z 1) (z 3)]) x ![p, a, b, c, d] =
      ∑ i, (D.covariantTensorDerivative D.riemannEvaluation x
          ![p, a, b, g.orthonormalBasis x i, d] * T x ![c, g.orthonormalBasis x i] +
        D.curvatureTensor x a b (g.orthonormalBasis x i) d *
          D.covariantTensorDerivative T x ![p, c, g.orthonormalBasis x i]) := by
  let U : CovariantTensorEvaluation n M 2 := fun y z => T y (z ∘ Equiv.swap 0 1)
  let L : CovariantTensorEvaluation n M 4 := fun y z =>
    U y ![D.curvature y (z 0) (z 1) (z 2), z 3]
  have hs : Fin.cons p (fun i : Fin 4 => ![p, a, b, c, d] ((Equiv.swap 2 3 i).succ)) =
      ![p, a, b, d, c] := by
    ext i
    fin_cases i <;> simp [Equiv.swap_apply_def] <;> rfl
  rw [D.curvature_action_right_perm T]
  change D.covariantTensorDerivative (fun y z => L y (z ∘ Equiv.swap 2 3)) x
    ![p, a, b, c, d] = _
  rw [D.covariantTensorDerivative_reindex]
  change D.covariantTensorDerivative (fun y z =>
      U y ![D.curvature y (z 0) (z 1) (z 2), z 3]) x
      (Fin.cons p (fun i => ![p, a, b, c, d] ((Equiv.swap 2 3 i).succ))) = _
  rw [hs, D.covariantTensorDerivative_curvature_action_left hD (hT.perm (Equiv.swap 0 1))]
  apply Finset.sum_congr rfl
  intro i _
  have hU : U x ![g.orthonormalBasis x i, c] = T x ![c, g.orthonormalBasis x i] := by
    change T x (![g.orthonormalBasis x i, c] ∘ Equiv.swap 0 1) = _
    congr 1
    ext j
    fin_cases j <;> simp [U, Equiv.swap_apply_def]
  have hDU : D.covariantTensorDerivative U x ![p, g.orthonormalBasis x i, c] =
      D.covariantTensorDerivative T x ![p, c, g.orthonormalBasis x i] := by
    rw [show U = (fun y z => T y (z ∘ Equiv.swap 0 1)) from rfl,
      D.covariantTensorDerivative_reindex]
    congr 1
    ext j
    fin_cases j <;> simp [Equiv.swap_apply_def] <;> rfl
  change _ * U x ![g.orthonormalBasis x i, c] +
    _ * D.covariantTensorDerivative U x ![p, g.orthonormalBasis x i, c] = _
  rw [hU, hDU]

lemma covariantTensorDerivative_curvature_action_two
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    {T : CovariantTensorEvaluation n M 2} (hT : IsSmoothCovariantTensor T)
    (x : M) (p a b c d : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (fun y z =>
        T y ![D.curvature y (z 0) (z 1) (z 2), z 3] +
          T y ![z 2, D.curvature y (z 0) (z 1) (z 3)]) x ![p, a, b, c, d] =
      ∑ i, (D.covariantTensorDerivative D.riemannEvaluation x
          ![p, a, b, g.orthonormalBasis x i, c] * T x ![g.orthonormalBasis x i, d] +
        D.curvatureTensor x a b (g.orthonormalBasis x i) c *
          D.covariantTensorDerivative T x ![p, g.orthonormalBasis x i, d] +
        D.covariantTensorDerivative D.riemannEvaluation x
          ![p, a, b, g.orthonormalBasis x i, d] * T x ![c, g.orthonormalBasis x i] +
        D.curvatureTensor x a b (g.orthonormalBasis x i) d *
          D.covariantTensorDerivative T x ![p, c, g.orthonormalBasis x i]) := by
  have hR : IsSmoothCovariantTensor (fun y (z : Fin 4 → TangentSpace (𝓡 n) y) =>
      T y ![z 2, D.curvature y (z 0) (z 1) (z 3)]) := by
    rw [D.curvature_action_right_perm T]
    exact (D.isSmooth_curvature_action_left hD (hT.perm (Equiv.swap 0 1))).perm (Equiv.swap 2 3)
  rw [D.covariantTensorDerivative_add (D.isSmooth_curvature_action_left hD hT) hR]
  dsimp only
  rw [D.covariantTensorDerivative_curvature_action_left hD hT,
    D.covariantTensorDerivative_curvature_action_right hD hT]
  simp only [Finset.sum_add_distrib]
  ring

end PoincareConjecture.LeviCivitaData
