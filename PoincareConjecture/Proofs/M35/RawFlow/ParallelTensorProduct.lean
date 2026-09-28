import PoincareConjecture.Proofs.M04.SectionalMinimumDiffusion
import PoincareConjecture.Proofs.M04.ScalarChainRule
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.Linearity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace PoincareConjecture.M35.Uniqueness

open M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private theorem tensor_extend_smooth {k : ℕ}
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T)
    (x : M) (v : Fin k → TangentSpace (𝓡 n) x) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => T y (fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i) y)) x := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  exact (hT.2 e.baseSet e.open_baseSet _ (fun i => contMDiffOn_extend_baseSet (v i))).contMDiffAt
    (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x))

theorem covariantTensorDerivative_scalar_mul (D : LeviCivitaData g) {k : ℕ}
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T)
    {f : M → ℝ} {x : M} (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x)
    (v : Fin (k + 1) → TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (fun y w => f y * T y w) x v =
      mvfderiv (𝓡 n) f x (v 0) * T x (fun i => v i.succ) +
        f x * D.covariantTensorDerivative T x v := by
  have ht := (tensor_extend_smooth hT x (fun i => v i.succ)).mdifferentiableAt (by simp)
  unfold LeviCivitaData.covariantTensorDerivative
  rw [mvfderiv_fun_mul (hf.mdifferentiableAt (by simp)) ht]
  simp only [add_apply, smul_apply, smul_eq_mul, FiberBundle.extend_apply_self,
    ← Finset.mul_sum]
  ring

theorem covariantTensorDerivative_scalar_mul_parallel (D : LeviCivitaData g) {k : ℕ}
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T)
    (hparallel : D.covariantTensorDerivative T = 0)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) :
    D.covariantTensorDerivative (fun y w => f y * T y w) =
      fun x v => mvfderiv (𝓡 n) f x (v 0) * T x (fun i => v i.succ) := by
  funext x v
  rw [covariantTensorDerivative_scalar_mul D hT (hf x), hparallel]
  simp only [Pi.zero_apply, mul_zero, add_zero]

theorem second_covariantTensorDerivative_scalar_mul_parallel
    (D : LeviCivitaData g) {k : ℕ}
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T)
    (hparallel : D.covariantTensorDerivative T = 0)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (x : M) (a b : TangentSpace (𝓡 n) x) (v : Fin k → TangentSpace (𝓡 n) x) :
    D.iteratedCovariantTensorDerivative (fun y w => f y * T y w) 2 x
        (Fin.cons a (Fin.cons b v)) = D.hessian f x a b * T x v := by
  let E := EuclideanSpace ℝ (Fin n)
  let B := FiberBundle.extend E b
  let V (i : Fin k) := FiberBundle.extend E (v i)
  let q : M → ℝ := fun y => mvfderiv (𝓡 n) f y (B y)
  let t : M → ℝ := fun y => T y (fun i => V i y)
  have hq : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) q x :=
    (contMDiffAt_directional_derivative (hf x)
      (FiberBundle.contMDiffAt_extend (k := ∞) (𝓡 n) E b)).mdifferentiableAt (by simp)
  have ht : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) t x :=
    (tensor_extend_smooth hT x v).mdifferentiableAt (by simp)
  have hdt : mvfderiv (𝓡 n) t x a =
      ∑ i, T x (Function.update v i (D.connection (V i) x a)) := by
    have hz := congrFun (congrFun hparallel x) (Fin.cons a v)
    simp only [LeviCivitaData.covariantTensorDerivative, Fin.cons_zero, Fin.cons_succ,
      Pi.zero_apply] at hz
    exact sub_eq_zero.mp hz
  have hd : mvfderiv (𝓡 n) (fun y => q y * t y) x a =
      mvfderiv (𝓡 n) q x a * T x v +
        mvfderiv (𝓡 n) f x b *
          ∑ i, T x (Function.update v i (D.connection (V i) x a)) := by
    rw [mvfderiv_fun_mul hq ht]
    simp only [add_apply, smul_apply, smul_eq_mul, q, B, t, V,
      FiberBundle.extend_apply_self]
    rw [hdt]
    ring
  change D.covariantTensorDerivative
    (D.covariantTensorDerivative (fun y w => f y * T y w)) x
      (Fin.cons a (Fin.cons b v)) = _
  rw [covariantTensorDerivative_scalar_mul_parallel D hT hparallel hf]
  simp only [LeviCivitaData.covariantTensorDerivative, Fin.cons_zero, Fin.cons_succ,
    Fin.sum_univ_succ, Fin.update_cons_zero, ← Fin.cons_update]
  change mvfderiv (𝓡 n) (fun y => q y * t y) x a -
    (mvfderiv (𝓡 n) f x (D.connection B x a) * T x v +
      ∑ i, mvfderiv (𝓡 n) f x b * T x (Function.update v i (D.connection (V i) x a))) = _
  rw [hd, ← Finset.mul_sum]
  simp only [LeviCivitaData.hessian, LeviCivitaData.hessianOnFields,
    FiberBundle.extend_apply_self]
  change _ = (mvfderiv (𝓡 n) q x a - mvfderiv (𝓡 n) f x (D.connection B x a)) * T x v
  ring

theorem tensorLaplacian_scalar_mul_parallel (D : LeviCivitaData g) {k : ℕ}
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T)
    (hparallel : D.covariantTensorDerivative T = 0)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (x : M) (v : Fin k → TangentSpace (𝓡 n) x) :
    D.tensorLaplacian (fun y w => f y * T y w) x v = D.laplacian f x * T x v := by
  simp only [LeviCivitaData.tensorLaplacian,
    second_covariantTensorDerivative_scalar_mul_parallel D hT hparallel hf,
    ← Finset.sum_mul, LeviCivitaData.laplacian]

theorem tensorLaplacian_scalar_mul_metricGram (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    D.tensorLaplacian (fun y w => f y * metricGramEvaluation g y w) x ![u, v, u, v] =
      D.laplacian f x * metricGram g x u v := by
  rw [tensorLaplacian_scalar_mul_parallel D (isSmoothCovariantTensor_metricGramEvaluation g)
    (covariantTensorDerivative_metricGramEvaluation D) hf]
  simp only [metricGramEvaluation, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    metricGram, g.symm x v u, pow_two]

theorem isSmoothCovariantTensor_scalar_mul {k : ℕ}
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) :
    IsSmoothCovariantTensor (fun x v => f x * T x v) := by
  constructor
  · intro x
    obtain ⟨A, hA⟩ := hT.1 x
    exact ⟨f x • A, fun v => by simp only [smul_apply, smul_eq_mul, hA]⟩
  · intro U hU X hX
    exact hf.contMDiffOn.mul (hT.2 U hU X hX)

theorem tensorLaplacian_add (D : LeviCivitaData g) {k : ℕ}
    {S T : CovariantTensorEvaluation n M k}
    (hS : IsSmoothCovariantTensor S) (hT : IsSmoothCovariantTensor T)
    (x : M) (v : Fin k → TangentSpace (𝓡 n) x) :
    D.tensorLaplacian (fun y w => S y w + T y w) x v =
      D.tensorLaplacian S x v + D.tensorLaplacian T x v := by
  simp only [LeviCivitaData.tensorLaplacian, LeviCivitaData.iteratedCovariantTensorDerivative]
  rw [D.covariantTensorDerivative_add hS hT,
    D.covariantTensorDerivative_add (isSmoothCovariantTensor_covariantTensorDerivative D hS)
      (isSmoothCovariantTensor_covariantTensorDerivative D hT)]
  exact Finset.sum_add_distrib

end PoincareConjecture.M35.Uniqueness
