import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

set_option autoImplicit false

open scoped Manifold ContDiff

namespace PoincareConjecture

theorem contMDiffAt_clm_of_apply_model
    {EB H B : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
    [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
    {IB : ModelWithCorners ℝ EB H}
    {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E]
    {f : B → E →L[ℝ] E'} {x : B}
    (hf : ∀ v, ContMDiffAt IB 𝓘(ℝ, E') ∞ (fun y => f y v) x) :
    ContMDiffAt IB 𝓘(ℝ, E →L[ℝ] E') ∞ f x := by
  let d := Module.finrank ℝ E
  have hd : d = Module.finrank ℝ (Fin d → ℝ) := (Module.finrank_fin_fun ℝ).symm
  let e₁ : E ≃L[ℝ] (Fin d → ℝ) := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : E' ≃L[ℝ] E')).trans (ContinuousLinearEquiv.piRing (Fin d))
  rw [← Function.id_comp f, ← e₂.symm_comp_self]
  exact e₂.symm.contDiff.contMDiff.contMDiffAt.comp x
    (contMDiffAt_pi_space.mpr fun i => hf _)

end PoincareConjecture
