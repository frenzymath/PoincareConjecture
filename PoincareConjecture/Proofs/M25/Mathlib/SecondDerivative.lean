import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

theorem fderiv_fderiv_comp_apply_of_contDiffOn
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {f : E → F} {g : F → G} {U : Set E} {V : Set F} {x : E}
    (hU : IsOpen U) (hV : IsOpen V) (hx : x ∈ U)
    (hf : ContDiffOn 𝕜 2 f U) (hg : ContDiffOn 𝕜 2 g V)
    (hmap : MapsTo f U V) (v w : E) :
    fderiv 𝕜 (fderiv 𝕜 (g ∘ f)) x v w =
      fderiv 𝕜 (fderiv 𝕜 g) (f x) (fderiv 𝕜 f x v) (fderiv 𝕜 f x w) +
        fderiv 𝕜 g (f x) (fderiv 𝕜 (fderiv 𝕜 f) x v w) := by
  have hfAt := hf.contDiffAt (hU.mem_nhds hx)
  have hgAt := hg.contDiffAt (hV.mem_nhds (hmap hx))
  have hDf := (hfAt.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)
  have hDg := (hgAt.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)
  have hcomp := (hDg.hasFDerivAt.comp x
    (hfAt.differentiableAt (by norm_num)).hasFDerivAt).clm_comp hDf.hasFDerivAt
  have heq : fderiv 𝕜 (g ∘ f) =ᶠ[𝓝 x]
      fun y => (fderiv 𝕜 g (f y)).comp (fderiv 𝕜 f y) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact fderiv_comp y
      ((hg.contDiffAt (hV.mem_nhds (hmap hy))).differentiableAt (by norm_num))
      ((hf.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))
  rw [heq.fderiv_eq]
  simpa [Function.comp_def, ContinuousLinearMap.comp_apply, add_comm] using
    congrArg (fun L : E →L[𝕜] E →L[𝕜] G => L v w) hcomp.fderiv
