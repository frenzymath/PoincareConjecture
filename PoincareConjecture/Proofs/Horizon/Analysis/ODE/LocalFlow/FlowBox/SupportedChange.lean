import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Topology.OpenPartialHomeomorph.Continuity

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace Poincare.ODE.LocalFlow

theorem exists_supported_vectorField_change
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : OpenPartialHomeomorph E F)
    (he : ContDiffOn ℝ ∞ e e.source)
    (hi : ContDiffOn ℝ ∞ e.symm e.target)
    {V : F → F} (hV : ContDiff ℝ ∞ V) (hVne : ∀ x, V x ≠ 0)
    {v : E} (hv : ∀ y ∈ e.source, fderiv ℝ e y v = V (e y))
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ e.source)
    {W : E → E} (hW : ContDiff ℝ ∞ W) (hWne : ∀ y, W y ≠ 0)
    (hWfix : ∀ y, y ∉ K → W y = v) :
    ∃ Z : F → F,
      ContDiff ℝ ∞ Z ∧
      (∀ x, Z x ≠ 0) ∧
      (∀ x, x ∉ e '' K → Z x = V x) ∧
      ∀ y ∈ e.source, Z (e y) = fderiv ℝ e y (W y) := by
  classical
  let Z : F → F := fun x =>
    if x ∈ e.target then fderiv ℝ e (e.symm x) (W (e.symm x)) else V x
  have hZchart (y : E) (hy : y ∈ e.source) :
      Z (e y) = fderiv ℝ e y (W y) := by
    simp only [Z, if_pos (e.map_source hy), e.left_inv hy]
  have hZfix (x : F) (hx : x ∉ e '' K) : Z x = V x := by
    by_cases hxt : x ∈ e.target
    · have hyK : e.symm x ∉ K := by
        intro hy
        exact hx ⟨e.symm x, hy, e.right_inv hxt⟩
      simp only [Z, if_pos hxt, hWfix _ hyK]
      rw [hv _ (e.map_target hxt), e.right_inv hxt]
    · simp only [Z, if_neg hxt]
  have hKclosed : IsClosed (e '' K) :=
    (hK.image_of_continuousOn (he.continuousOn.mono hKs)).isClosed
  refine ⟨Z, ?_, ?_, hZfix, hZchart⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ e.target
    · have hye : ContDiffAt ℝ ∞ e (e.symm x) :=
        he.contDiffAt (e.open_source.mem_nhds (e.map_target hx))
      have hxi : ContDiffAt ℝ ∞ e.symm x :=
        hi.contDiffAt (e.open_target.mem_nhds hx)
      have hs : ContDiffAt ℝ ∞
          (fun z => fderiv ℝ e (e.symm z) (W (e.symm z))) x :=
        ((hye.fderiv_right (by simp)).clm_apply hW.contDiffAt).comp x hxi
      apply hs.congr_of_eventuallyEq
      filter_upwards [e.open_target.mem_nhds hx] with z hz
      exact if_pos hz
    · have hxK : x ∉ e '' K := by
        rintro ⟨y, hy, rfl⟩
        exact hx (e.map_source (hKs hy))
      apply hV.contDiffAt.congr_of_eventuallyEq
      filter_upwards [hKclosed.isOpen_compl.mem_nhds hxK] with z hz
      exact hZfix z hz
  · intro x
    by_cases hx : x ∈ e.target
    · let y := e.symm x
      have hy : y ∈ e.source := e.map_target hx
      have hde := (he.contDiffAt (e.open_source.mem_nhds hy)).differentiableAt
        (by simp)
      have hdi := (hi.contDiffAt (e.open_target.mem_nhds (e.map_source hy))).differentiableAt
        (by simp)
      have hid : HasFDerivAt (fun z => e.symm (e z))
          (ContinuousLinearMap.id ℝ E) y :=
        (hasFDerivAt_id y).congr_of_eventuallyEq (e.eventually_left_inverse hy)
      have hleft := (hdi.hasFDerivAt.comp y hde.hasFDerivAt).unique hid
      intro hzero
      have hpushed : fderiv ℝ e y (W y) = 0 := by
        simpa only [Z, if_pos hx] using hzero
      have hwy := congrArg (fun L : E →L[ℝ] E => L (W y)) hleft
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
        hpushed, map_zero] at hwy
      exact hWne y hwy.symm
    · simpa only [Z, if_neg hx] using hVne x

end Poincare.ODE.LocalFlow
