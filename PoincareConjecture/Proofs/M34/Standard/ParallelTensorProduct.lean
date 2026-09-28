import PoincareConjecture.Proofs.M34.Standard.TensorScalarProduct
import PoincareConjecture.Proofs.M04.ScalarHessian

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem covariantTensorDerivative_differential_mul_parallel {k : ℕ}
    (D : LeviCivitaData g) {T : CovariantTensorEvaluation n M k}
    (hT : IsSmoothCovariantTensor T) (hpar : D.covariantTensorDerivative T = 0)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (x : M) (a b : TangentSpace (𝓡 n) x) (v : Fin k → TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative
      (fun y (w : Fin (k + 1) → TangentSpace (𝓡 n) y) =>
        mvfderiv (𝓡 n) f y (w 0) * T y (fun i => w i.succ)) x
      (Fin.cons a (Fin.cons b v)) = D.hessian f x a b * T x v := by
  let E := EuclideanSpace ℝ (Fin n)
  let Y := FiberBundle.extend E b
  let Z := fun i => FiberBundle.extend E (v i)
  let p := fun y => mvfderiv (𝓡 n) f y (Y y)
  let q := fun y => T y (fun i => Z i y)
  have hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% Y) x :=
    FiberBundle.contMDiffAt_extend (k := ∞) (𝓡 n) E b
  have hp := (M04.contMDiffAt_directional_derivative (hf x) hY).mdifferentiableAt (by simp)
  have hq := (hT.contMDiffAt_canonicalExtensions x v).mdifferentiableAt (by simp)
  have hprod := mvfderiv_fun_mul hp hq
  have hparx := congrFun (congrFun hpar x) (Fin.cons a v)
  have hqderiv : mvfderiv (𝓡 n) q x a =
      ∑ i, T x (Function.update v i (D.connection (Z i) x a)) := by
    change mvfderiv (𝓡 n) q x a -
      ∑ i, T x (Function.update v i (D.connection (Z i) x a)) = 0 at hparx
    exact sub_eq_zero.mp hparx
  simp only [covariantTensorDerivative, Fin.cons_zero, Fin.cons_succ,
    Fin.sum_univ_succ, Fin.update_cons_zero, ← Fin.cons_update]
  change mvfderiv (𝓡 n) (fun y => p y * q y) x a -
    (mvfderiv (𝓡 n) f x (D.connection Y x a) * T x v +
      ∑ i, mvfderiv (𝓡 n) f x b *
        T x (Function.update v i (D.connection (Z i) x a))) = _
  rw [hprod]
  simp only [add_apply, smul_apply, smul_eq_mul]
  change p x * mvfderiv (𝓡 n) q x a + q x * mvfderiv (𝓡 n) p x a - _ = _
  rw [hqderiv, ← Finset.mul_sum]
  simp only [p, q, Y, Z, FiberBundle.extend_apply_self]
  simp only [hessian, hessianOnFields, FiberBundle.extend_apply_self]
  ring

theorem tensorLaplacian_smoothScalar_mul_parallel {k : ℕ}
    (D : LeviCivitaData g) {T : CovariantTensorEvaluation n M k}
    (hT : IsSmoothCovariantTensor T) (hpar : D.covariantTensorDerivative T = 0)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (x : M) (v : Fin k → TangentSpace (𝓡 n) x) :
    D.tensorLaplacian (fun y w => f y * T y w) x v = D.laplacian f x * T x v := by
  have hfirst : D.covariantTensorDerivative (fun y w => f y * T y w) =
      fun y w => mvfderiv (𝓡 n) f y (w 0) * T y (fun i => w i.succ) := by
    funext y w
    rw [D.covariantTensorDerivative_smoothScalar_mul hT hf, hpar]
    simp
  simp only [tensorLaplacian, iteratedCovariantTensorDerivative, hfirst,
    D.covariantTensorDerivative_differential_mul_parallel hT hpar hf,
    laplacian, Finset.sum_mul]

end PoincareConjecture.LeviCivitaData
