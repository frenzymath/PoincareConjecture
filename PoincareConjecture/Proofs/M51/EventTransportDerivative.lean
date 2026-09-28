import PoincareConjecture.Proofs.M35.Mathlib.DiffeomorphDerivative





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



theorem mfderiv_precomp (e : Diffeomorph I₁ I₂ M₁ M₂ n) (hn : n ≠ 0)
    (f : M₂ → M₃) (x : M₁) :
    mfderiv I₁ I₃ (f ∘ e) x =
      (mfderiv I₂ I₃ f (e x)).comp (mfderiv I₁ I₂ e x) := by
  by_cases hf : MDifferentiableAt I₂ I₃ f (e x)
  · exact _root_.mfderiv_comp x hf (e.contMDiff.mdifferentiable hn x)
  · have hcomp : ¬ MDifferentiableAt I₁ I₃ (f ∘ e) x := by
      intro h
      have hback := h.comp_of_eq (e x) (e.symm.contMDiff.mdifferentiable hn _)
        (e.symm_apply_apply x)
      have heq : (f ∘ e) ∘ e.symm = f := funext (fun y => congrArg f (e.apply_symm_apply y))
      rw [heq] at hback
      exact hf hback
    rw [mfderiv_zero_of_not_mdifferentiableAt hcomp,
      mfderiv_zero_of_not_mdifferentiableAt hf, ContinuousLinearMap.zero_comp]

end Diffeomorph
