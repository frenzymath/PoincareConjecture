import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Analysis.Calculus.FDeriv.Mul










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold

namespace PoincareConjecture.M60



theorem mfderiv_comp_smul
    {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    {I : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (f : E → M) (c : ℝ) (z : E) :
    mfderiv 𝓘(ℝ, E) I (fun x => f (c • x)) z =
      c • mfderiv 𝓘(ℝ, E) I f (c • z) := by
  have hs (a : ℝ) (x : E) : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E)
      (fun y : E => a • y) x (a • ContinuousLinearMap.id ℝ E) :=
    ((hasFDerivAt_id x).const_smul a).hasMFDerivAt
  by_cases hc : c = 0
  · subst c
    have heq : (fun x : E => f ((0 : ℝ) • x)) = (fun _ : E => f 0) := by
      funext x
      rw [zero_smul]
    simp only [zero_smul]
    rw [heq]
    exact mfderiv_const
  by_cases hf : MDifferentiableAt 𝓘(ℝ, E) I f (c • z)
  · change mfderiv 𝓘(ℝ, E) I (f ∘ (fun x => c • x)) z = _
    erw [mfderiv_comp z hf (hs c z).mdifferentiableAt, (hs c z).mfderiv]
    ext v
    simp only [ContinuousLinearMap.comp_apply, smul_apply, map_smul]
    rfl
  · have hcomp : ¬MDifferentiableAt 𝓘(ℝ, E) I (fun x => f (c • x)) z := by
      intro h
      have hback := h.comp_of_eq (c • z) (hs c⁻¹ (c • z)).mdifferentiableAt
        (show c⁻¹ • (c • z) = z by simp [hc])
      apply hf
      simpa only [Function.comp_def, smul_inv_smul₀ hc] using hback
    rw [mfderiv_zero_of_not_mdifferentiableAt hcomp, mfderiv_zero_of_not_mdifferentiableAt hf,
      smul_zero]

end PoincareConjecture.M60
