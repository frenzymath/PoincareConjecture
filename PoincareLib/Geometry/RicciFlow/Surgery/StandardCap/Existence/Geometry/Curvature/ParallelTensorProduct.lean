import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Curvature.TensorScalarProduct
import PoincareLib.Geometry.RicciFlow.Curvature.Calculus.Identities.ScalarHessian
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Curvature.Calculus.Fields.ConnectionScalar
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Curvature.Calculus.Fields.FixedExtension
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Curvature.Calculus.Tensors.TensorDerivativeClosure

/-!
# The Laplacian of a scalar times a parallel tensor

The covariant product rule leaves only the scalar Hessian when the tensor
factor is parallel. Its orthonormal trace is exactly the frozen scalar
Laplacian. This is the variable-shift diffusion preparation for
Morgan-Tian Lemma 12.6, pp. 297-298.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- Covariantly differentiating the differential times a parallel tensor
leaves the actual scalar Hessian times that tensor
(Lemma 12.6, pp. 297-298). -/
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

/-- A smooth scalar times a parallel actual tensor has tensor Laplacian
equal to the scalar Laplacian times the tensor
(Lemma 12.6, pp. 297-298). -/
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

end PoincareMT.LeviCivitaData
