
import PoincareConjecture.Definitions.Ch01.TensorRegularity









set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private lemma IsSmoothCovariantTensor.contMDiffAt_extend {k : ℕ}
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T)
    (x : M) (v : Fin k → TangentSpace (𝓡 n) x) :
    ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞
      (fun y ↦ T y (fun i ↦ FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i) y)) x := by
  classical
  choose s hs hsm using fun i ↦
    FiberBundle.exists_contMDiffOn_extend (k := ∞) (𝓡 n)
      (EuclideanSpace ℝ (Fin n)) (v i)
  let U : Set M := ⋂ i, interior (s i)
  have hU : IsOpen U := isOpen_iInter_of_finite fun _ ↦ isOpen_interior
  have hx : x ∈ U := Set.mem_iInter.mpr fun i ↦
    mem_interior_iff_mem_nhds.mpr (hs i)
  apply (hT.2 U hU
    (fun i y ↦ FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i) y) ?_).contMDiffAt
    (hU.mem_nhds hx)
  intro i
  exact (hsm i).mono fun y hy ↦ interior_subset (Set.mem_iInter.mp hy i)

lemma covariantTensorDerivative_sub {k : ℕ}
    (D : LeviCivitaData g) {S T : CovariantTensorEvaluation n M k}
    (hS : IsSmoothCovariantTensor S) (hT : IsSmoothCovariantTensor T) :
    D.covariantTensorDerivative (fun x v ↦ S x v - T x v) =
      fun x v ↦ D.covariantTensorDerivative S x v -
        D.covariantTensorDerivative T x v := by
  funext x v
  unfold covariantTensorDerivative
  have hSx := (IsSmoothCovariantTensor.contMDiffAt_extend hS x (fun i ↦ v i.succ))
  have hTx := (IsSmoothCovariantTensor.contMDiffAt_extend hT x (fun i ↦ v i.succ))
  have hderiv :
      mvfderiv (𝓡 n) (fun y ↦ (S y (fun i ↦
        FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i.succ) y) -
        T y (fun i ↦ FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i.succ) y))) x
        (v 0) =
      mvfderiv (𝓡 n) (fun y ↦ S y (fun i ↦
        FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i.succ) y)) x (v 0) -
        mvfderiv (𝓡 n) (fun y ↦ T y (fun i ↦
        FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i.succ) y)) x (v 0) := by
    have hfun : (fun y ↦ S y (fun i ↦
        FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i.succ) y) -
        T y (fun i ↦ FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i.succ) y)) =
        (fun y ↦ S y (fun i ↦ FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i.succ) y)) -
        (fun y ↦ T y (fun i ↦ FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i.succ) y)) := by
      funext y
      rfl
    rw [hfun]
    have hm := mvfderiv_sub (hSx.mdifferentiableAt (by simp))
      (hTx.mdifferentiableAt (by simp))
    simpa [mvfderiv, Pi.sub_apply] using congrArg (fun L ↦ L (v 0)) hm
  rw [hderiv]
  rw [Finset.sum_sub_distrib]
  ring

lemma covariantTensorDerivative_add {k : ℕ}
    (D : LeviCivitaData g) {S T : CovariantTensorEvaluation n M k}
    (hS : IsSmoothCovariantTensor S) (hT : IsSmoothCovariantTensor T) :
    D.covariantTensorDerivative (fun y z => S y z + T y z) =
      fun y z => D.covariantTensorDerivative S y z + D.covariantTensorDerivative T y z := by
  funext x v
  have h := mvfderiv_fun_add
    ((IsSmoothCovariantTensor.contMDiffAt_extend hS x (fun i => v i.succ)).mdifferentiableAt (by simp))
    ((IsSmoothCovariantTensor.contMDiffAt_extend hT x (fun i => v i.succ)).mdifferentiableAt (by simp))
  simp only [covariantTensorDerivative, h, add_apply, Finset.sum_add_distrib]
  ring

lemma covariantTensorDerivative_const_mul {k : ℕ}
    (D : LeviCivitaData g) {T : CovariantTensorEvaluation n M k}
    (hT : IsSmoothCovariantTensor T) (c : ℝ) :
    D.covariantTensorDerivative (fun y z => c * T y z) =
      fun y z => c * D.covariantTensorDerivative T y z := by
  funext x v
  have h := mvfderiv_fun_mul (mdifferentiableAt_const (c := c))
    ((IsSmoothCovariantTensor.contMDiffAt_extend hT x (fun i => v i.succ)).mdifferentiableAt (by simp))
  simp only [covariantTensorDerivative, h, mvfderiv_const, smul_zero, add_zero,
    smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

lemma covariantTensorDerivative_reindex {k : ℕ}
    (D : LeviCivitaData g) (T : CovariantTensorEvaluation n M k)
    (σ : Equiv.Perm (Fin k)) (x : M)
    (v : Fin (k + 1) → TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative
        (fun y w ↦ T y (w ∘ σ)) x v =
      D.covariantTensorDerivative T x
        (Fin.cons (v 0) (fun i ↦ v (σ i).succ)) := by
  simp only [covariantTensorDerivative, Fin.cons_succ, Fin.cons_zero]
  congr 1
  rw [← Equiv.sum_comp σ]
  apply Finset.sum_congr rfl
  intro i hi
  congr 2
  funext j
  simp only [Function.update_apply, Function.comp_apply]
  by_cases hji : σ j = i
  · subst i
    simp [σ.injective.eq_iff]
  · simp

end PoincareConjecture.LeviCivitaData
