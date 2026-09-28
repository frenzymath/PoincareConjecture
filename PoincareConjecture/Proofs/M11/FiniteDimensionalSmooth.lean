import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace





set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Module Function
open scoped Manifold ContDiff

namespace PoincareConjecture.Proofs.M11

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E]
  {k : WithTop ℕ∞}

theorem contMDiffWithinAt_clm_of_apply {f : B → E →L[ℝ] F} {s : Set B} {p : B}
    (h : ∀ v, ContMDiffWithinAt IB 𝓘(ℝ, F) k (fun x ↦ f x v) s p) :
    ContMDiffWithinAt IB 𝓘(ℝ, E →L[ℝ] F) k f s p := by
  let d := finrank ℝ E
  have hd : d = finrank ℝ (Fin d → ℝ) := (finrank_fin_fun ℝ).symm
  let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : F ≃L[ℝ] F)).trans (ContinuousLinearEquiv.piRing (Fin d))
  rw [← id_comp f, ← e₂.symm_comp_self]
  exact e₂.symm.contDiff.contMDiff.contMDiffAt.comp_contMDiffWithinAt p
    (contMDiffWithinAt_pi_space.mpr fun i ↦ h _)

theorem contMDiffAt_clm_of_apply {f : B → E →L[ℝ] F} {p : B}
    (h : ∀ v, ContMDiffAt IB 𝓘(ℝ, F) k (fun x ↦ f x v) p) :
    ContMDiffAt IB 𝓘(ℝ, E →L[ℝ] F) k f p := by
  let d := finrank ℝ E
  have hd : d = finrank ℝ (Fin d → ℝ) := (finrank_fin_fun ℝ).symm
  let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : F ≃L[ℝ] F)).trans (ContinuousLinearEquiv.piRing (Fin d))
  rw [← id_comp f, ← e₂.symm_comp_self]
  exact e₂.symm.contDiff.contMDiff.contMDiffAt.comp p (contMDiffAt_pi_space.mpr fun i ↦ h _)

theorem contMDiffOn_clm_of_apply {f : B → E →L[ℝ] F} {s : Set B}
    (h : ∀ v, ContMDiffOn IB 𝓘(ℝ, F) k (fun x ↦ f x v) s) :
    ContMDiffOn IB 𝓘(ℝ, E →L[ℝ] F) k f s := by
  let d := finrank ℝ E
  have hd : d = finrank ℝ (Fin d → ℝ) := (finrank_fin_fun ℝ).symm
  let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : F ≃L[ℝ] F)).trans (ContinuousLinearEquiv.piRing (Fin d))
  rw [← id_comp f, ← e₂.symm_comp_self]
  exact e₂.symm.contDiff.contMDiff.comp_contMDiffOn (contMDiffOn_pi_space.mpr fun i ↦ h _)

end PoincareConjecture.Proofs.M11
