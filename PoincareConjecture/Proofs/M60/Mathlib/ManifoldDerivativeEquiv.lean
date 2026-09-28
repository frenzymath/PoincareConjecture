import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Analysis.Calculus.FDeriv.Equiv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold

namespace PoincareConjecture.M60

theorem mfderiv_comp_continuousLinearEquiv
    {E E' F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    {I : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    (f : E' → M) (e : E ≃L[ℝ] E') (z : E) :
    mfderiv 𝓘(ℝ, E) I (fun x => f (e x)) z =
      (mfderiv 𝓘(ℝ, E') I f (e z)).comp e.toContinuousLinearMap := by
  have he : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E') e z e.toContinuousLinearMap :=
    e.hasFDerivAt.hasMFDerivAt
  by_cases hf : MDifferentiableAt 𝓘(ℝ, E') I f (e z)
  · change mfderiv 𝓘(ℝ, E) I (f ∘ e) z = _
    erw [mfderiv_comp z hf he.mdifferentiableAt, he.mfderiv]
  · have hcomp : ¬MDifferentiableAt 𝓘(ℝ, E) I (fun x => f (e x)) z := by
      intro h
      have hback := h.comp_of_eq (e z) e.symm.hasFDerivAt.hasMFDerivAt.mdifferentiableAt
        (e.symm_apply_apply z)
      apply hf
      simpa only [Function.comp_def, e.apply_symm_apply] using hback
    rw [mfderiv_zero_of_not_mdifferentiableAt hcomp, mfderiv_zero_of_not_mdifferentiableAt hf,
      ContinuousLinearMap.zero_comp]

end PoincareConjecture.M60
