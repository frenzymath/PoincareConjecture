import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Total manifold derivatives through a diffeomorphism

The coordinate transfer in Morgan-Tian Theorem 12.28, pp. 323-324,
uses total maps outside their neck domains. Postcomposition by a
diffeomorphism preserves nondifferentiability, so the totalized chain
rule also holds at those points without changing either map.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  {E₃ : Type*} [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃]
  {H₁ : Type*} [TopologicalSpace H₁] {H₂ : Type*} [TopologicalSpace H₂]
  {H₃ : Type*} [TopologicalSpace H₃]
  {I₁ : ModelWithCorners 𝕜 E₁ H₁} {I₂ : ModelWithCorners 𝕜 E₂ H₂}
  {I₃ : ModelWithCorners 𝕜 E₃ H₃}
  {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
  {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  {M₃ : Type*} [TopologicalSpace M₃] [ChartedSpace H₃ M₃]
  {n : ℕ∞ω}

/-- The totalized chain rule for postcomposition by a diffeomorphism.
Used for the unchanged neck coordinates in Theorem 12.28, pp. 323-324. -/
theorem mfderiv_comp (e : Diffeomorph I₂ I₃ M₂ M₃ n) (hn : n ≠ 0)
    (f : M₁ → M₂) (x : M₁) :
    mfderiv I₁ I₃ (e ∘ f) x =
      (mfderiv I₂ I₃ e (f x)).comp (mfderiv I₁ I₂ f x) := by
  by_cases hf : MDifferentiableAt I₁ I₂ f x
  · exact _root_.mfderiv_comp x (e.contMDiff.mdifferentiable hn _) hf
  · have hcomp : ¬ MDifferentiableAt I₁ I₃ (e ∘ f) x := by
      intro h
      have hback := (e.symm.contMDiff.mdifferentiable hn _).comp x h
      have heq : e.symm ∘ (e ∘ f) = f := funext (fun y => e.symm_apply_apply (f y))
      rw [heq] at hback
      exact hf hback
    rw [mfderiv_zero_of_not_mdifferentiableAt hcomp,
      mfderiv_zero_of_not_mdifferentiableAt hf, ContinuousLinearMap.comp_zero]

/-- The derivatives of a coordinate diffeomorphism and its inverse cancel
even when the subsequent total map is not differentiable. Used in the
actual pullback transfer of Theorem 12.28, pp. 323-324. -/
theorem mfderiv_cancel_left (e : Diffeomorph I₂ I₃ M₂ M₃ n) (hn : n ≠ 0)
    (f : M₁ → M₃) (x : M₁) :
    (mfderiv I₂ I₃ e (e.symm (f x))).comp (mfderiv I₁ I₂ (e.symm ∘ f) x) =
      mfderiv I₁ I₃ f x := by
  have h := e.mfderiv_comp (I₁ := I₁) hn (e.symm ∘ f) x
  have heq : e ∘ (e.symm ∘ f) = f := funext (fun y => e.apply_symm_apply (f y))
  rw [heq] at h
  exact h.symm

end Diffeomorph
