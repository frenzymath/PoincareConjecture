import PoincareConjecture.Definitions.Ch01.TensorOperators
import Mathlib.LinearAlgebra.Multilinear.Basic

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

def IsSmoothCovariantTensor {k : ℕ} (T : CovariantTensorEvaluation n M k) : Prop :=
  (∀ x : M, ∃ A : MultilinearMap ℝ (fun _ : Fin k ↦ TangentSpace (𝓡 n) x) ℝ,
    ∀ v, T x v = A v) ∧
  ∀ U : Set M, IsOpen U →
    ∀ X : Fin k → (x : M) → TangentSpace (𝓡 n) x,
      (∀ i, ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓘(ℝ, EuclideanSpace ℝ (Fin n))))
        ∞ (T% (X i)) U) →
      ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞ (fun x ↦ T x (fun i ↦ X i x)) U

end PoincareConjecture
