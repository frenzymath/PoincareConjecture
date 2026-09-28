import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

open scoped ContDiff

namespace PoincareConjecture.Proofs.M09

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem exists_smooth_local_inverse (f : E → F) (S : Set E) (hS : IsOpen S)
    (hf : ContDiffOn ℝ ∞ f S) (x : E) (hx : x ∈ S)
    (hbij : Function.Bijective (fderiv ℝ f x)) :
    ∃ e : OpenPartialHomeomorph E F, x ∈ e.source ∧ e.source ⊆ S ∧
      (e : E → F) = f ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ y ∈ e.source, Function.Bijective (fderiv ℝ f y) := by
  let L : E ≃L[ℝ] F :=
    (LinearEquiv.ofBijective (fderiv ℝ f x).toLinearMap hbij).toContinuousLinearEquiv
  have hL : (L : E →L[ℝ] F) = fderiv ℝ f x := by ext v; rfl
  have hfx : ContDiffAt ℝ ∞ f x := hf.contDiffAt (hS.mem_nhds hx)
  have hdx : HasFDerivAt f (L : E →L[ℝ] F) x := by
    rw [hL]
    exact (hfx.differentiableAt (by simp)).hasFDerivAt
  let e0 := hfx.toOpenPartialHomeomorph f hdx (by simp)
  let V := S ∩ (fderiv ℝ f) ⁻¹' {L : E →L[ℝ] F | Function.Injective L}
  have hV : IsOpen V :=
    (hf.continuousOn_fderiv_of_isOpen hS (by simp)).isOpen_inter_preimage hS
      ContinuousLinearMap.isOpen_injective
  have hxV : x ∈ V := ⟨hx, hbij.1⟩
  let e := e0.restrOpen V hV
  have he : (e : E → F) = f := rfl
  have hsub : e.source ⊆ S := fun y hy ↦ hy.2.1
  have hdimb : Module.finrank ℝ E = Module.finrank ℝ F := L.toLinearEquiv.finrank_eq
  have hb (y : E) (hy : y ∈ e.source) : Function.Bijective (fderiv ℝ f y) :=
    ⟨hy.2.2, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (fderiv ℝ f y).toLinearMap) hdimb).mp hy.2.2⟩
  refine ⟨e, ⟨hfx.mem_toOpenPartialHomeomorph_source hdx (by simp), hxV⟩,
    hsub, he, ?_, hb⟩
  intro y hy
  have hx' : e.symm y ∈ S := hsub (e.map_target hy)
  have hsmooth : ContDiffAt ℝ ∞ f (e.symm y) := hf.contDiffAt (hS.mem_nhds hx')
  let L' : E ≃L[ℝ] F := (LinearEquiv.ofBijective (fderiv ℝ f (e.symm y)).toLinearMap
    (hb (e.symm y) (e.map_target hy))).toContinuousLinearEquiv
  have hL' : (L' : E →L[ℝ] F) = fderiv ℝ f (e.symm y) := by ext v; rfl
  apply (e.contDiffAt_symm hy (f₀' := L') ?_ ?_).contDiffWithinAt
  · rw [he, hL']
    exact (hsmooth.differentiableAt (by simp)).hasFDerivAt
  · rwa [he]

end PoincareConjecture.Proofs.M09
