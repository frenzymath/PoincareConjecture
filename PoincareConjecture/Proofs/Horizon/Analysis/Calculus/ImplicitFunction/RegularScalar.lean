import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff












open Set Function Filter
open scoped Topology ContDiff

namespace Poincare.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]


theorem exists_smooth_superlevel_chart {f : E → ℝ} {V : Set E} (hV : IsOpen V)
    (hf : ContDiffOn ℝ ∞ f V) {a : E} (ha : a ∈ V)
    (hreg : Surjective (fderiv ℝ f a)) :
    ∃ e : OpenPartialHomeomorph E (ℝ × (fderiv ℝ f a).ker),
      a ∈ e.source ∧ e.source ⊆ V ∧ e a = (f a, 0) ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ x ∈ e.source, (e x).1 = f x) ∧
      ∀ c : ℝ, e '' (e.source ∩ {x | c ≤ f x}) = e.target ∩ {y | c ≤ y.1} := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  let L := fderiv ℝ f a
  have hfa : ContDiffAt ℝ ∞ f a := (hf a ha).contDiffAt (hV.mem_nhds ha)
  have hstrict : HasStrictFDerivAt f L a := hfa.hasStrictFDerivAt (by simp)
  have hL : L.range = ⊤ := LinearMap.range_eq_top.mpr hreg
  let P := L.ker_closedComplemented_of_finiteDimensional_range
  let d := hstrict.implicitFunctionDataOfComplemented f L hL P
  let g := d.prodFun
  let e0 := d.toOpenPartialHomeomorph
  have hg : ContDiffOn ℝ ∞ g V := by
    exact hf.prodMk (((Classical.choose P).contDiff.comp
      (contDiff_id.sub contDiff_const)).contDiffOn)
  have hgderiv := d.hasStrictFDerivAt.hasFDerivAt
  have hgInv : (fderiv ℝ g a).IsInvertible := d.isInvertible_fderiv_prodFun
  let W := V ∩ (fderiv ℝ g) ⁻¹' range
    ((↑) : (E ≃L[ℝ] (ℝ × L.ker)) → E →L[ℝ] (ℝ × L.ker))
  have hW : IsOpen W :=
    (hg.continuousOn_fderiv_of_isOpen hV (by simp)).isOpen_inter_preimage
      hV ContinuousLinearEquiv.isOpen
  have haW : a ∈ W := ⟨ha, hgInv⟩
  let e := e0.restrOpen W hW
  have hes : e.source ⊆ V := fun x hx => hx.2.1
  have hecoe : (e : E → ℝ × L.ker) = g := rfl
  have heforward : ContDiffOn ℝ ∞ e e.source := by
    rw [hecoe]
    exact hg.mono hes
  refine ⟨e, ⟨d.pt_mem_toOpenPartialHomeomorph_source, haW⟩, hes, ?_, heforward,
    ?_, ?_, ?_⟩
  · change (f a, (Classical.choose P) (a - a)) = (f a, 0)
    simp
  · intro y hy
    have hys : e.symm y ∈ e.source := e.map_target hy
    obtain ⟨A, hA⟩ := hys.2.2
    have hgAt := (hg (e.symm y) (hes hys)).contDiffAt (hV.mem_nhds (hes hys))
    apply (e.contDiffAt_symm hy (f₀' := A) ?_ ?_).contDiffWithinAt
    · rw [hecoe, hA]
      exact (hgAt.differentiableAt (by simp)).hasFDerivAt
    · rw [hecoe]
      exact hgAt
  · intro x hx
    rfl
  · intro c
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hcx⟩, rfl⟩
      exact ⟨e.map_source hx, hcx⟩
    · rintro ⟨hy, hcy⟩
      refine ⟨e.symm y, ⟨e.map_target hy, ?_⟩, e.right_inv hy⟩
      have heq : f (e.symm y) = y.1 := congrArg Prod.fst (e.right_inv hy)
      simpa [heq] using hcy


end Poincare.Analysis
