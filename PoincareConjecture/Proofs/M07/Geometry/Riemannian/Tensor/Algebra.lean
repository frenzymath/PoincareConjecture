import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.Regularity
import Mathlib.Geometry.Manifold.Algebra.Structures








set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.IsSmoothCovariantTensor

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {k : ℕ} {S T : CovariantTensorEvaluation n M k}

lemma sub (hS : IsSmoothCovariantTensor S) (hT : IsSmoothCovariantTensor T) :
    IsSmoothCovariantTensor (fun x v ↦ S x v - T x v) := by
  constructor
  · intro x
    obtain ⟨A, hA⟩ := hS.1 x
    obtain ⟨B, hB⟩ := hT.1 x
    exact ⟨A - B, fun v ↦ by simp only [hA, hB, sub_apply]⟩
  · intro U hU X hX
    exact (hS.2 U hU X hX).sub (hT.2 U hU X hX)

lemma add (hS : IsSmoothCovariantTensor S) (hT : IsSmoothCovariantTensor T) :
    IsSmoothCovariantTensor (fun x v => S x v + T x v) := by
  constructor
  · intro x
    obtain ⟨A, hA⟩ := hS.1 x
    obtain ⟨B, hB⟩ := hT.1 x
    exact ⟨A + B, fun v => by simp only [hA, hB, add_apply]⟩
  · intro U hU X hX
    exact (hS.2 U hU X hX).add (hT.2 U hU X hX)

lemma const_mul (hT : IsSmoothCovariantTensor T) (c : ℝ) :
    IsSmoothCovariantTensor (fun x v => c * T x v) := by
  constructor
  · intro x
    obtain ⟨A, hA⟩ := hT.1 x
    exact ⟨c • A, fun v => by simp only [hA, smul_apply, smul_eq_mul]⟩
  · intro U hU X hX
    exact contMDiffOn_const.mul (hT.2 U hU X hX)

lemma perm (hT : IsSmoothCovariantTensor T) (σ : Equiv.Perm (Fin k)) :
    IsSmoothCovariantTensor (fun x v ↦ T x (v ∘ σ)) := by
  constructor
  · intro x
    obtain ⟨A, hA⟩ := hT.1 x
    exact ⟨A.domDomCongr σ, fun v ↦ hA _⟩
  · intro U hU X hX
    exact hT.2 U hU (fun i ↦ X (σ i)) (fun i ↦ hX (σ i))

end PoincareConjecture.IsSmoothCovariantTensor
