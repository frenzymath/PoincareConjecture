import PoincareLib.Geometry.Riemannian.Tensor.Operations
import Mathlib.LinearAlgebra.Multilinear.Basic

/-! Source: Mapher06/Poincare-MorganTian, `PoincareMT/Definitions/Ch01/TensorRegularity.lean`,
revision `b2c3c64781fee22edfd683a224d4f8d280e2e9ce`. Only imports and module placement are changed.
See `references/ricci-flow/mapher/shared-foundations.json`. -/


/-!
# Smoothness of raw covariant tensor evaluations

Pointwise multilinearity and smoothness on local smooth sections are expressed
as propositions. No bundled tensor is constructed with admitted proof fields.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- Multilinear evaluations whose values on arbitrary local smooth sections are smooth. -/
def IsSmoothCovariantTensor {k : ℕ} (T : CovariantTensorEvaluation n M k) : Prop :=
  (∀ x : M, ∃ A : MultilinearMap ℝ (fun _ : Fin k ↦ TangentSpace (𝓡 n) x) ℝ,
    ∀ v, T x v = A v) ∧
  ∀ U : Set M, IsOpen U →
    ∀ X : Fin k → (x : M) → TangentSpace (𝓡 n) x,
      (∀ i, ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓘(ℝ, EuclideanSpace ℝ (Fin n))))
        ∞ (T% (X i)) U) →
      ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞ (fun x ↦ T x (fun i ↦ X i x)) U

end PoincareMT
