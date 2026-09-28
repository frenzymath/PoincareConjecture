import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.ProductDerivative
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Trace.Double
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.MaximumPrinciple.DerivativeRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.MaximumPrinciple.HilbertFiber

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

namespace RiemannianMetric

def tensorPairingTwo (g : RiemannianMetric n M)
    (S T : CovariantTensorEvaluation n M 2) (x : M) : ℝ :=
  ∑ i, ∑ j, S x ![g.orthonormalBasis x i, g.orthonormalBasis x j] *
    T x ![g.orthonormalBasis x i, g.orthonormalBasis x j]

def tensorPairingCovector (g : RiemannianMetric n M)
    (F : CovariantTensorEvaluation n M 3) (Z : CovariantTensorEvaluation n M 2) :
    CovariantTensorEvaluation n M 1 :=
  fun x v => ∑ i, ∑ j,
    F x ![v 0, g.orthonormalBasis x i, g.orthonormalBasis x j] *
      Z x ![g.orthonormalBasis x i, g.orthonormalBasis x j]

def tensorPairingThree (g : RiemannianMetric n M)
    (F G : CovariantTensorEvaluation n M 3) (x : M) : ℝ :=
  ∑ a, ∑ i, ∑ j,
    F x ![g.orthonormalBasis x a, g.orthonormalBasis x i, g.orthonormalBasis x j] *
      G x ![g.orthonormalBasis x a, g.orthonormalBasis x i, g.orthonormalBasis x j]

theorem tensorPairingTwo_self_nonneg
    (g : RiemannianMetric n M) (T : CovariantTensorEvaluation n M 2) (x : M) :
    0 ≤ g.tensorPairingTwo T T x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_self_nonneg _

theorem tensorPairingTwo_self_eq_tensorNorm_sq
    (g : RiemannianMetric n M) (T : CovariantTensorEvaluation n M 2) (x : M) :
    g.tensorPairingTwo T T x = g.tensorNorm T x ^ 2 := by
  classical
  rw [tensorNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  let I := Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))
  have h := Fintype.sum_equiv (finTwoArrowEquiv I)
    (fun a => (T x (fun k => g.orthonormalBasis x (a k))) ^ 2)
    (fun p => (T x ![g.orthonormalBasis x p.1, g.orthonormalBasis x p.2]) ^ 2)
    (fun a => by
      congr 2
      ext k
      fin_cases k <;> rfl)
  rw [h, Fintype.sum_prod_type]
  simp only [tensorPairingTwo, pow_two]
  rfl

end RiemannianMetric

private def pairingTwoPermutation : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective ![0, 2, 1, 3] (by decide)

private def pairingCovectorPermutation : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective ![4, 0, 2, 1, 3] (by decide)

private theorem tensorPairingTwo_eq_trace
    (S T : CovariantTensorEvaluation n M 2) :
    (fun x (_ : Fin 0 → TangentSpace (𝓡 n) x) => g.tensorPairingTwo S T x) =
      g.tensorTrace (g.tensorTrace (fun x v =>
        tensorProduct S T x (v ∘ pairingTwoPermutation))) := by
  funext x v
  dsimp only [RiemannianMetric.tensorTrace, RiemannianMetric.tensorPairingTwo]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [tensorProduct]
  congr 1
  · congr 1
    ext k
    fin_cases k <;> rfl
  · congr 1
    ext k
    fin_cases k <;> rfl

private theorem tensorPairingCovector_eq_trace
    (F : CovariantTensorEvaluation n M 3) (Z : CovariantTensorEvaluation n M 2) :
    g.tensorPairingCovector F Z =
      g.tensorTrace (g.tensorTrace (fun x v =>
        tensorProduct F Z x (v ∘ pairingCovectorPermutation))) := by
  funext x v
  dsimp only [RiemannianMetric.tensorTrace, RiemannianMetric.tensorPairingCovector]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [tensorProduct]
  congr 1
  · congr 1
    ext k
    fin_cases k <;> rfl
  · congr 1
    ext k
    fin_cases k <;> rfl

namespace LeviCivitaData

theorem contMDiff_tensorPairingTwo (_D : LeviCivitaData g)
    {S T : CovariantTensorEvaluation n M 2}
    (hS : IsSmoothCovariantTensor S) (hT : IsSmoothCovariantTensor T) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (g.tensorPairingTwo S T) := by
  have hP := (isSmoothCovariantTensor_tensorProduct hS hT).perm pairingTwoPermutation
  have htrace := (hP.tensorTrace (g := g)).tensorTrace (g := g)
  rw [← tensorPairingTwo_eq_trace S T] at htrace
  exact contMDiffOn_univ.mp
    (htrace.2 Set.univ isOpen_univ (fun i => Fin.elim0 i) (fun i => Fin.elim0 i))

theorem isSmoothCovariantTensor_tensorPairingCovector (_D : LeviCivitaData g)
    {F : CovariantTensorEvaluation n M 3} {Z : CovariantTensorEvaluation n M 2}
    (hF : IsSmoothCovariantTensor F) (hZ : IsSmoothCovariantTensor Z) :
    IsSmoothCovariantTensor (g.tensorPairingCovector F Z) := by
  rw [tensorPairingCovector_eq_trace F Z]
  exact (((isSmoothCovariantTensor_tensorProduct hF hZ).perm
    pairingCovectorPermutation).tensorTrace (g := g)).tensorTrace

theorem mvfderiv_tensorPairingTwo (D : LeviCivitaData g)
    {S T : CovariantTensorEvaluation n M 2}
    (hS : IsSmoothCovariantTensor S) (hT : IsSmoothCovariantTensor T)
    (x : M) (u : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) (g.tensorPairingTwo S T) x u =
      g.tensorPairingCovector (D.covariantTensorDerivative S) T x ![u] +
      g.tensorPairingCovector (D.covariantTensorDerivative T) S x ![u] := by
  have hP := (isSmoothCovariantTensor_tensorProduct hS hT).perm pairingTwoPermutation
  have h := D.covariantTensorDerivative_tensorTrace_tensorTrace hP x u ![]
  rw [← tensorPairingTwo_eq_trace S T] at h
  have hscalar : D.covariantTensorDerivative
      (fun y (_ : Fin 0 → TangentSpace (𝓡 n) y) => g.tensorPairingTwo S T y)
        x (Fin.cons u ![]) = mvfderiv (𝓡 n) (g.tensorPairingTwo S T) x u := by
    simp only [covariantTensorDerivative, Fin.cons_zero, Fin.sum_univ_zero, sub_zero]
  rw [hscalar] at h
  rw [h]
  have hterm (i j) :
      D.covariantTensorDerivative
        (fun y v => tensorProduct S T y (v ∘ pairingTwoPermutation)) x
          ![u, g.orthonormalBasis x i, g.orthonormalBasis x i,
            g.orthonormalBasis x j, g.orthonormalBasis x j] =
        D.covariantTensorDerivative S x
            ![u, g.orthonormalBasis x i, g.orthonormalBasis x j] *
          T x ![g.orthonormalBasis x i, g.orthonormalBasis x j] +
        S x ![g.orthonormalBasis x i, g.orthonormalBasis x j] *
          D.covariantTensorDerivative T x
            ![u, g.orthonormalBasis x i, g.orthonormalBasis x j] := by
    rw [D.covariantTensorDerivative_reindex]
    have hv :
        Fin.cons u (fun k : Fin 4 =>
          ![u, g.orthonormalBasis x i, g.orthonormalBasis x i,
            g.orthonormalBasis x j, g.orthonormalBasis x j]
            (pairingTwoPermutation k).succ) =
          ![u, g.orthonormalBasis x i, g.orthonormalBasis x j,
            g.orthonormalBasis x i, g.orthonormalBasis x j] := by
      ext k
      fin_cases k <;> rfl
    change D.covariantTensorDerivative (tensorProduct S T) x
      (Fin.cons u (fun k : Fin 4 =>
        ![u, g.orthonormalBasis x i, g.orthonormalBasis x i,
          g.orthonormalBasis x j, g.orthonormalBasis x j]
          (pairingTwoPermutation k).succ)) = _
    rw [hv]
    change D.covariantTensorDerivative (tensorProduct S T) x
      (Fin.cons u ![g.orthonormalBasis x i, g.orthonormalBasis x j,
        g.orthonormalBasis x i, g.orthonormalBasis x j]) = _
    rw [D.covariantTensorDerivative_tensorProduct hS hT]
    congr 1
    · congr 1
      · congr 1
        ext k
        fin_cases k <;> rfl
      · congr 1
        ext k
        fin_cases k <;> rfl
    · congr 1
      · congr 1
        ext k
        fin_cases k <;> rfl
      · congr 1
        ext k
        fin_cases k <;> rfl
  change (∑ i, ∑ j, D.covariantTensorDerivative
    (fun y v => tensorProduct S T y (v ∘ pairingTwoPermutation)) x
      ![u, g.orthonormalBasis x i, g.orthonormalBasis x i,
        g.orthonormalBasis x j, g.orthonormalBasis x j]) = _
  simp_rw [hterm, Finset.sum_add_distrib]
  simp only [RiemannianMetric.tensorPairingCovector, Matrix.cons_val_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem covariantTensorDerivative_tensorPairingCovector (D : LeviCivitaData g)
    {F : CovariantTensorEvaluation n M 3} {Z : CovariantTensorEvaluation n M 2}
    (hF : IsSmoothCovariantTensor F) (hZ : IsSmoothCovariantTensor Z)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (g.tensorPairingCovector F Z) x ![u, v] =
      ∑ i, ∑ j,
        (D.covariantTensorDerivative F x
            ![u, v, g.orthonormalBasis x i, g.orthonormalBasis x j] *
          Z x ![g.orthonormalBasis x i, g.orthonormalBasis x j] +
        F x ![v, g.orthonormalBasis x i, g.orthonormalBasis x j] *
          D.covariantTensorDerivative Z x
            ![u, g.orthonormalBasis x i, g.orthonormalBasis x j]) := by
  have hP := (isSmoothCovariantTensor_tensorProduct hF hZ).perm pairingCovectorPermutation
  have h := D.covariantTensorDerivative_tensorTrace_tensorTrace hP x u ![v]
  rw [← tensorPairingCovector_eq_trace F Z] at h
  simp only [Matrix.Fin.cons_vecCons] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [D.covariantTensorDerivative_reindex]
  have hv :
      Fin.cons u (fun k : Fin 5 =>
        ![u, g.orthonormalBasis x i, g.orthonormalBasis x i,
          g.orthonormalBasis x j, g.orthonormalBasis x j, v]
          (pairingCovectorPermutation k).succ) =
        ![u, v, g.orthonormalBasis x i, g.orthonormalBasis x j,
          g.orthonormalBasis x i, g.orthonormalBasis x j] := by
    ext k
    fin_cases k <;> rfl
  change D.covariantTensorDerivative (tensorProduct F Z) x
    (Fin.cons u (fun k : Fin 5 =>
      ![u, g.orthonormalBasis x i, g.orthonormalBasis x i,
        g.orthonormalBasis x j, g.orthonormalBasis x j, v]
        (pairingCovectorPermutation k).succ)) = _
  rw [hv]
  change D.covariantTensorDerivative (tensorProduct F Z) x
    (Fin.cons u ![v, g.orthonormalBasis x i, g.orthonormalBasis x j,
      g.orthonormalBasis x i, g.orthonormalBasis x j]) = _
  rw [D.covariantTensorDerivative_tensorProduct hF hZ]
  congr 1
  · congr 1
    · congr 1
      ext k
      fin_cases k <;> rfl
    · congr 1
      ext k
      fin_cases k <;> rfl
  · congr 1
    · congr 1
      ext k
      fin_cases k <;> rfl
    · congr 1
      ext k
      fin_cases k <;> rfl

theorem tensorTrace_derivative_tensorPairingCovector (D : LeviCivitaData g)
    {F : CovariantTensorEvaluation n M 3} {Z : CovariantTensorEvaluation n M 2}
    (hF : IsSmoothCovariantTensor F) (hZ : IsSmoothCovariantTensor Z) (x : M) :
    g.tensorTrace (D.covariantTensorDerivative (g.tensorPairingCovector F Z)) x ![] =
      g.tensorPairingTwo (g.tensorTrace (D.covariantTensorDerivative F)) Z x +
        g.tensorPairingThree F (D.covariantTensorDerivative Z) x := by
  change (∑ i, D.covariantTensorDerivative (g.tensorPairingCovector F Z) x
    ![g.orthonormalBasis x i, g.orthonormalBasis x i]) = _
  simp_rw [D.covariantTensorDerivative_tensorPairingCovector hF hZ,
    Finset.sum_add_distrib]
  dsimp only [RiemannianMetric.tensorPairingThree]
  congr 1
  dsimp only [RiemannianMetric.tensorPairingTwo, RiemannianMetric.tensorTrace]
  simp only [Finset.sum_mul, Matrix.Fin.cons_vecCons]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

end LeviCivitaData
end PoincareConjecture
