import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.TangentCone.Prod

set_option autoImplicit false

open Set
open scoped ContDiff

namespace PoincareConjecture.SpacetimeBounds

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiffOn_spatialFDeriv_within {f : ℝ × V → E} {J : Set ℝ} {U : Set V}
    (hf : ContDiffOn ℝ ∞ f (J ×ˢ U)) (hJ : UniqueDiffOn ℝ J) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (fun z : ℝ × V ↦ fderiv ℝ (fun x ↦ f (z.1, x)) z.2)
      (J ×ˢ U) := by
  have hd := (hf.fderivWithin (hJ.prod hU.uniqueDiffOn) (m := ∞) (by simp)).clm_comp
    (contDiffOn_const (c := ContinuousLinearMap.inr ℝ ℝ V))
  apply hd.congr
  intro z hz
  have hcomp := ((hf z hz).differentiableWithinAt (by simp)).hasFDerivWithinAt.comp z.2
    (((hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id z.2)).hasFDerivWithinAt)
    (show MapsTo (fun x : V ↦ (z.1, x)) U (J ×ˢ U) from fun _ hx ↦ ⟨hz.1, hx⟩)
  exact (hcomp.hasFDerivAt (hU.mem_nhds hz.2)).fderiv

end PoincareConjecture.SpacetimeBounds
