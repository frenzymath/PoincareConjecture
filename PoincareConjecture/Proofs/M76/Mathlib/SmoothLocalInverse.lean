import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

set_option autoImplicit false

open Set
open scoped Topology ContDiff

namespace ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_smooth_openPartialHomeomorph {f : E → F} {n : ℕ∞ω}
    (hf : ContDiff ℝ n f) (hn : n ≠ 0) {x : E} (A : E ≃L[ℝ] F)
    (hA : HasFDerivAt f (A : E →L[ℝ] F) x) :
    ∃ e : OpenPartialHomeomorph E F, (e : E → F) = f ∧ x ∈ e.source ∧
      ContDiffOn ℝ n e.symm e.target := by
  let V := {y : E | (fderiv ℝ f y).IsInvertible}
  have hV : IsOpen V := ContinuousLinearEquiv.isOpen.preimage (hf.continuous_fderiv hn)
  let e := (hf.contDiffAt.toOpenPartialHomeomorph f hA hn).restrOpen V hV
  refine ⟨e, rfl, ?_, ?_⟩
  · refine ⟨hf.contDiffAt.mem_toOpenPartialHomeomorph_source hA hn, ?_⟩
    change (fderiv ℝ f x).IsInvertible
    rw [hA.fderiv]
    exact ContinuousLinearMap.isInvertible_equiv
  · intro y hy
    have hmem := e.map_target hy
    obtain ⟨B, hB⟩ := hmem.2
    apply ContDiffAt.contDiffWithinAt
    apply e.contDiffAt_symm (f₀' := B) hy
    · change HasFDerivAt f (B : E →L[ℝ] F) (e.symm y)
      rw [hB]
      exact (hf.differentiable hn).differentiableAt.hasFDerivAt
    · exact hf.contDiffAt

theorem exists_smooth_openPartialHomeomorph_on {f : E → F} {n : ℕ∞ω}
    (hf : ContDiff ℝ n f) (hn : n ≠ 0) {U : Set E} (hU : IsOpen U)
    (hinj : InjOn f U) (hderiv : ∀ x ∈ U, (fderiv ℝ f x).IsInvertible) :
    ∃ e : OpenPartialHomeomorph E F, (e : E → F) = f ∧ e.source = U ∧
      ContDiffOn ℝ n e.symm e.target := by
  have hopen : IsOpenMap (U.domRestrict f) := by
    rw [isOpenMap_iff_nhds_le]
    intro x
    obtain ⟨A, hA⟩ := hderiv x x.property
    have hd : HasFDerivAt f (A : E →L[ℝ] F) x := by
      rw [hA]
      exact (hf.differentiable hn).differentiableAt.hasFDerivAt
    have hs := hf.contDiffAt.hasStrictFDerivAt' hd hn
    change 𝓝 (f x) ≤ Filter.map (f ∘ Subtype.val) (𝓝 x)
    rw [← Filter.map_map, hU.isOpenEmbedding_subtypeVal.map_nhds_eq,
      hs.map_nhds_eq_of_equiv]
  let e := OpenPartialHomeomorph.ofContinuousOpenRestrict (hinj.toPartialEquiv f U)
    hf.continuous.continuousOn hopen hU
  refine ⟨e, rfl, rfl, ?_⟩
  intro y hy
  obtain ⟨B, hB⟩ := hderiv (e.symm y) (e.map_target hy)
  apply ContDiffAt.contDiffWithinAt
  apply e.contDiffAt_symm (f₀' := B) hy
  · change HasFDerivAt f (B : E →L[ℝ] F) (e.symm y)
    rw [hB]
    exact (hf.differentiable hn).differentiableAt.hasFDerivAt
  · exact hf.contDiffAt

end ContDiff
