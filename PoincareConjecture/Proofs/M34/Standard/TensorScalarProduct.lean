import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.Linearity
import PoincareConjecture.Proofs.M04.TensorDerivativeClosure
import Mathlib.Geometry.Manifold.Algebra.Structures

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem IsSmoothCovariantTensor.mul_smoothScalar {k : ℕ}
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) :
    IsSmoothCovariantTensor (fun x v => f x * T x v) := by
  constructor
  · intro x
    obtain ⟨A, hA⟩ := hT.1 x
    exact ⟨f x • A, fun v => by simp only [hA, smul_apply, smul_eq_mul]⟩
  · intro U hU X hX
    exact hf.contMDiffOn.mul (hT.2 U hU X hX)

theorem IsSmoothCovariantTensor.sub_tensor {k : ℕ}
    {S T : CovariantTensorEvaluation n M k} (hS : IsSmoothCovariantTensor S)
    (hT : IsSmoothCovariantTensor T) :
    IsSmoothCovariantTensor (fun x v => S x v - T x v) := by
  constructor
  · intro x
    obtain ⟨A, hA⟩ := hS.1 x
    obtain ⟨B, hB⟩ := hT.1 x
    exact ⟨A - B, fun v => by simp only [hA, hB, sub_apply]⟩
  · intro U hU X hX
    exact (hS.2 U hU X hX).sub (hT.2 U hU X hX)

theorem IsSmoothCovariantTensor.contMDiffAt_canonicalExtensions {k : ℕ}
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T)
    (x : M) (v : Fin k → TangentSpace (𝓡 n) x) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => T y (fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i) y)) x := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hs := hT.2 e.baseSet e.open_baseSet _ (fun i => M04.contMDiffOn_extend_baseSet (v i))
  exact hs.contMDiffAt (e.open_baseSet.mem_nhds hx)

namespace LeviCivitaData

variable {g : RiemannianMetric n M}

theorem covariantTensorDerivative_smoothScalar_mul {k : ℕ}
    (D : LeviCivitaData g) {T : CovariantTensorEvaluation n M k}
    (hT : IsSmoothCovariantTensor T) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (v : Fin (k + 1) → TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (fun y w => f y * T y w) x v =
      mvfderiv (𝓡 n) f x (v 0) * T x (fun i => v i.succ) +
        f x * D.covariantTensorDerivative T x v := by
  have hprod := mvfderiv_fun_mul ((hf x).mdifferentiableAt (by simp))
    ((hT.contMDiffAt_canonicalExtensions x (fun i => v i.succ)).mdifferentiableAt (by simp))
  simp only [covariantTensorDerivative, hprod, add_apply, smul_apply, smul_eq_mul,
    FiberBundle.extend_apply_self, ← Finset.mul_sum]
  ring

theorem tensorLaplacian_sub_tensor {k : ℕ} (D : LeviCivitaData g)
    {S T : CovariantTensorEvaluation n M k} (hS : IsSmoothCovariantTensor S)
    (hT : IsSmoothCovariantTensor T) (x : M) (v : Fin k → TangentSpace (𝓡 n) x) :
    D.tensorLaplacian (fun y w => S y w - T y w) x v =
      D.tensorLaplacian S x v - D.tensorLaplacian T x v := by
  have hDS := M04.isSmoothCovariantTensor_covariantTensorDerivative D hS
  have hDT := M04.isSmoothCovariantTensor_covariantTensorDerivative D hT
  simp only [tensorLaplacian, iteratedCovariantTensorDerivative,
    D.covariantTensorDerivative_sub hS hT, D.covariantTensorDerivative_sub hDS hDT,
    Finset.sum_sub_distrib]

end LeviCivitaData
end PoincareConjecture
