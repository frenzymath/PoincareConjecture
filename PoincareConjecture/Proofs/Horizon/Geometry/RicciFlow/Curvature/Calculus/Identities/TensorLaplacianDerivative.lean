import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Identities.ScalarContractions

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private def laplacianSlotPermutation (k : ℕ) : Equiv.Perm (Fin (k + 2)) :=
  (finCongr (Nat.add_comm k 2)).trans (finAddFlip (m := 2) (n := k))

private theorem append_comp_laplacianSlotPermutation {α : Type*} {k : ℕ}
    (v : Fin k → α) (a b : α) :
    Fin.append v ![a, b] ∘ laplacianSlotPermutation k =
      Fin.cons a (Fin.cons b v) := by
  funext i
  cases i using Fin.cases with
  | zero =>
    change Fin.append v ![a, b]
      (finAddFlip (Fin.cast (Nat.add_comm k 2) (0 : Fin (k + 2)))) = a
    rw [show Fin.cast (Nat.add_comm k 2) (0 : Fin (k + 2)) =
      Fin.castAdd k (0 : Fin 2) from rfl,
      finAddFlip_apply_castAdd, Fin.append_right]
    rfl
  | succ i =>
    cases i using Fin.cases with
    | zero =>
      change Fin.append v ![a, b]
        (finAddFlip (Fin.cast (Nat.add_comm k 2) (1 : Fin (k + 2)))) = b
      rw [show Fin.cast (Nat.add_comm k 2) (1 : Fin (k + 2)) =
        Fin.castAdd k (1 : Fin 2) from rfl,
        finAddFlip_apply_castAdd, Fin.append_right]
      rfl
    | succ i =>
      change Fin.append v ![a, b]
        (finAddFlip (Fin.cast (Nat.add_comm k 2) i.succ.succ)) = v i
      have hi : Fin.cast (Nat.add_comm k 2) i.succ.succ = Fin.natAdd 2 i := by
        apply Fin.ext
        simp only [Fin.val_cast, Fin.val_succ, Fin.val_natAdd]
        omega
      rw [hi, finAddFlip_apply_natAdd, Fin.append_left]

private theorem tensorLaplacian_eq_trace (D : LeviCivitaData g)
    {k : ℕ} (T : CovariantTensorEvaluation n M k) :
    D.tensorLaplacian T =
      tensorTraceLast g
        (tensorPermute (D.iteratedCovariantTensorDerivative T 2)
          (laplacianSlotPermutation k)) := by
  funext x v
  simp only [LeviCivitaData.tensorLaplacian, tensorTraceLast, tensorPermute,
    append_comp_laplacianSlotPermutation]

theorem isSmoothCovariantTensor_tensorLaplacian (D : LeviCivitaData g)
    {k : ℕ} {T : CovariantTensorEvaluation n M k}
    (hT : IsSmoothCovariantTensor T) :
    IsSmoothCovariantTensor (D.tensorLaplacian T) := by
  rw [tensorLaplacian_eq_trace D T]
  exact isSmoothCovariantTensor_tensorTraceLast g
    (isSmoothCovariantTensor_tensorPermute
      (isSmoothCovariantTensor_covariantTensorDerivative D
        (isSmoothCovariantTensor_covariantTensorDerivative D hT))
      (laplacianSlotPermutation k))

set_option backward.isDefEq.respectTransparency false in
theorem covariantTensorDerivative_tensorLaplacian (D : LeviCivitaData g)
    {k : ℕ} {T : CovariantTensorEvaluation n M k}
    (hT : IsSmoothCovariantTensor T) (x : M)
    (a : TangentSpace (𝓡 n) x) (v : Fin k → TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (D.tensorLaplacian T) x (Fin.cons a v) =
      ∑ i, D.iteratedCovariantTensorDerivative T 3 x
        (Fin.cons a (Fin.cons (g.orthonormalBasis x i)
          (Fin.cons (g.orthonormalBasis x i) v))) := by
  classical
  have hK : IsSmoothCovariantTensor (D.iteratedCovariantTensorDerivative T 2) :=
    isSmoothCovariantTensor_covariantTensorDerivative D
      (isSmoothCovariantTensor_covariantTensorDerivative D hT)
  rw [tensorLaplacian_eq_trace D T,
    covariantTensorDerivative_tensorTraceLast D
      (isSmoothCovariantTensor_tensorPermute hK (laplacianSlotPermutation k))]
  unfold tensorTraceLast
  apply Finset.sum_congr rfl
  intro i _
  have hAppend :
      Fin.append (Fin.cons a v) ![g.orthonormalBasis x i, g.orthonormalBasis x i] =
        Fin.cons a (Fin.append v ![g.orthonormalBasis x i, g.orthonormalBasis x i]) := by
    simpa only [Fin.cast_refl, Function.comp_id] using
      Fin.append_cons a v ![g.orthonormalBasis x i, g.orthonormalBasis x i]
  rw [hAppend, covariantTensorDerivative_tensorPermute D hK,
    append_comp_laplacianSlotPermutation]
  rfl

end PoincareConjecture.RicciFlowAnalysis
