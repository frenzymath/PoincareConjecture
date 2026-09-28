import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.MaximumPrinciple.DerivativeRegularity
import PoincareConjecture.Definitions.Ch01.ScalarOperators

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle Filter

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

lemma secondCovariantTensorDerivative_on_fields
    (D : LeviCivitaData g) {k : ℕ} {T : CovariantTensorEvaluation n M k}
    (hT : IsSmoothCovariantTensor T)
    (W : Fin k → (y : M) → TangentSpace (𝓡 n) y) (x : M)
    (hW : ∀ i, ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% (W i)) x)
    (a b : TangentSpace (𝓡 n) x) :
    let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) b
    let f := fun y => T y (fun i => W i y)
    D.covariantTensorDerivative (D.covariantTensorDerivative T) x
        (Fin.cons a (Fin.cons b (fun i => W i x))) =
      D.hessian f x a b -
        mvfderiv (𝓡 n) (fun y => ∑ i, T y
          (Function.update (fun j => W j y) i
            (D.covariantDerivativeOnFields Y (W i) y))) x a +
        ∑ i, T x (Function.update (fun j => W j x) i
          (D.connection (W i) x (D.connection Y x a))) -
        ∑ i, D.covariantTensorDerivative T x
          (Fin.cons b (Function.update (fun j => W j x) i (D.connection (W i) x a))) := by
  classical
  have hDT := D.covariantTensorDerivative_isSmooth hT
  dsimp only
  let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) b
  let f := fun y => T y (fun i => W i y)
  have hY := FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) b
  have hupdate (i : Fin k) : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => T y (Function.update (fun j => W j y) i
        (D.covariantDerivativeOnFields Y (W i) y))) x := by
    have h := hT.contMDiffAt_apply (x := x) (X := Function.update W i
      (D.covariantDerivativeOnFields Y (W i))) (fun j => by
        by_cases hj : j = i
        · simpa only [hj, Function.update_self] using
            D.contMDiffAt_covariantDerivativeOnFields hY (hW i)
        · simpa only [Function.update_of_ne hj] using hW j)
    convert h using 1
    funext y
    congr 1
    ext j
    by_cases hj : j = i <;> simp [hj, Function.update_of_ne]
  have heq : (fun y => D.covariantTensorDerivative T y
      (Fin.cons (Y y) (fun i => W i y))) =ᶠ[𝓝 x]
      (fun y => mvfderiv (𝓡 n) f y (Y y) -
        ∑ i, T y (Function.update (fun j => W j y) i
          (D.covariantDerivativeOnFields Y (W i) y))) := by
    filter_upwards [Filter.eventually_all.mpr
      (fun i => eventually_mdifferentiableAt_of_contMDiffAt (hW i))] with y hy
    exact D.covariantTensorDerivative_on_fields hT W y hy (Y y)
  have hderiv : mvfderiv (𝓡 n) (fun y => D.covariantTensorDerivative T y
      (Fin.cons (Y y) (fun i => W i y))) x =
      mvfderiv (𝓡 n) (fun y => mvfderiv (𝓡 n) f y (Y y) -
        ∑ i, T y (Function.update (fun j => W j y) i
          (D.covariantDerivativeOnFields Y (W i) y))) x := by
    unfold mvfderiv
    rw [heq.mfderiv_eq]
    congr 2
  have houter := D.covariantTensorDerivative_on_fields hDT (Fin.cons Y W) x
    (by intro i; cases i using Fin.cases
        · exact hY.mdifferentiableAt (by simp)
        · exact (hW _).mdifferentiableAt (by simp)) a
  have hfirst := D.covariantTensorDerivative_on_fields hT W x
    (fun i => (hW i).mdifferentiableAt (by simp)) (D.connection Y x a)
  dsimp only [Y] at hfirst
  have heval (y : M) : (fun i : Fin (k + 1) =>
      (Fin.cons Y W : Fin (k + 1) → (z : M) → TangentSpace (𝓡 n) z) i y) =
      Fin.cons (Y y) (fun i => W i y) := by
    ext i
    cases i using Fin.cases <;> rfl
  simp only [heval, Y, FiberBundle.extend_apply_self] at houter
  rw [houter, hderiv, mvfderiv_fun_sub
    ((contMDiffAt_mvfderiv_apply (hT.contMDiffAt_apply hW) hY).mdifferentiableAt (by simp))
    ((ContMDiffAt.sum (t := Finset.univ) fun i _ => hupdate i).mdifferentiableAt (by simp))]
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.update_cons_zero,
    ← Fin.cons_update, hfirst, sub_apply]
  simp only [hessian, hessianOnFields, FiberBundle.extend_apply_self, Y]
  ring

lemma secondCovariantTensorDerivative_eq_hessian_of_zero_jets
    (D : LeviCivitaData g) {k : ℕ} {T : CovariantTensorEvaluation n M k}
    (hT : IsSmoothCovariantTensor T)
    (W : Fin k → (y : M) → TangentSpace (𝓡 n) y) (x : M)
    (hW : ∀ i, ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% (W i)) x)
    (a : TangentSpace (𝓡 n) x)
    (hfirst : ∀ i v, D.connection (W i) x v = 0)
    (hsecond : ∀ i, D.connection
      (D.covariantDerivativeOnFields
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a) (W i)) x a = 0) :
    D.covariantTensorDerivative (D.covariantTensorDerivative T) x
        (Fin.cons a (Fin.cons a (fun i => W i x))) =
      D.hessian (fun y => T y (fun i => W i y)) x a a := by
  classical
  have hDT := D.covariantTensorDerivative_isSmooth hT
  let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a
  let Z := fun i => D.covariantDerivativeOnFields X (W i)
  have hX := FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) a
  have hZ i := D.contMDiffAt_covariantDerivativeOnFields hX (hW i)
  obtain ⟨A, hA⟩ := hT.1 x
  obtain ⟨B, hB⟩ := hDT.1 x
  have hZzero (i : Fin k) : Z i x = 0 := by
    simpa only [Z, X, covariantDerivativeOnFields, FiberBundle.extend_apply_self] using
      hfirst i a
  have hslot (i : Fin k) : mvfderiv (𝓡 n)
      (fun y => T y (Function.update (fun j => W j y) i (Z i y))) x a = 0 := by
    have heval (y : M) : (fun j => Function.update W i (Z i) j y) =
        Function.update (fun j => W j y) i (Z i y) := by
      ext j
      by_cases hj : j = i <;> simp [hj, Function.update_of_ne]
    have h := D.covariantTensorDerivative_on_fields hT (Function.update W i (Z i)) x
      (fun j => by
        by_cases hj : j = i
        · simpa only [hj, Function.update_self] using (hZ i).mdifferentiableAt (by simp)
        · simpa only [Function.update_of_ne hj] using (hW j).mdifferentiableAt (by simp)) a
    have hconn (j : Fin k) : D.connection (Function.update W i (Z i) j) x a = 0 := by
      by_cases hj : j = i
      · simpa only [hj, Function.update_self, Z, X] using hsecond i
      · simpa only [Function.update_of_ne hj] using hfirst j a
    simp only [heval, hconn, hA, A.map_update_zero, Finset.sum_const_zero, sub_zero,
      hZzero, Fin.cons_update, hB, B.map_update_zero] at h
    exact h.symm
  have hsum : mvfderiv (𝓡 n)
      (fun y => ∑ i, T y (Function.update (fun j => W j y) i (Z i y))) x a = 0 := by
    rw [mvfderiv_sum_apply]
    · simp only [hslot, Finset.sum_const_zero]
    · intro i
      have h := hT.mdifferentiableAt_apply (x := x) (X := Function.update W i (Z i))
        (fun j => by
          by_cases hj : j = i
          · simpa only [hj, Function.update_self] using (hZ i).mdifferentiableAt (by simp)
          · simpa only [Function.update_of_ne hj] using (hW j).mdifferentiableAt (by simp))
      convert h using 1
      funext y
      congr 1
      ext j
      by_cases hj : j = i <;> simp [hj, Function.update_of_ne]
  rw [D.secondCovariantTensorDerivative_on_fields hT W x hW a a]
  change _ - _ + _ - _ = _
  rw [hsum]
  simp only [hfirst, hA, A.map_update_zero, Finset.sum_const_zero, sub_zero, add_zero,
    Fin.cons_update, hB, B.map_update_zero]

lemma tensorLaplacian_eq_laplacian_of_zero_jets
    (D : LeviCivitaData g) {k : ℕ} {T : CovariantTensorEvaluation n M k}
    (hT : IsSmoothCovariantTensor T)
    (W : Fin k → (y : M) → TangentSpace (𝓡 n) y) (x : M)
    (hW : ∀ i, ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% (W i)) x)
    (hfirst : ∀ i v, D.connection (W i) x v = 0)
    (hsecond : ∀ i v, D.connection
      (D.covariantDerivativeOnFields
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) (W i)) x v = 0) :
    D.tensorLaplacian T x (fun i => W i x) =
      D.laplacian (fun y => T y (fun i => W i y)) x := by
  unfold tensorLaplacian laplacian
  apply Finset.sum_congr rfl
  intro j _
  exact D.secondCovariantTensorDerivative_eq_hessian_of_zero_jets hT W x hW
    (g.orthonormalBasis x j) hfirst (fun i => hsecond i _)

end PoincareConjecture.LeviCivitaData
