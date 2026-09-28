import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM









set_option autoImplicit false

open Set Filter
open scoped Topology

universe u v

namespace PoincareConjecture.M63

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]




theorem fixedComposition_second_derivative {S : Set E} {U : Set F}
    (hS : IsOpen S) (hU : IsOpen U) {f : E → F} {r : F → F}
    (hf : ContDiffOn ℝ 2 f S) (hr : ContDiffOn ℝ 2 r U)
    (hfU : MapsTo f S U) (hfix : ∀ y ∈ S, r (f y) = f y)
    {y : E} (hy : y ∈ S) :
    (∀ v : E, fderiv ℝ r (f y) (fderiv ℝ f y v) = fderiv ℝ f y v) ∧
    ∀ v w c : E,
      fderiv ℝ (fderiv ℝ r) (f y) (fderiv ℝ f y v) (fderiv ℝ f y w) +
        fderiv ℝ r (f y)
          (fderiv ℝ (fderiv ℝ f) y v w - fderiv ℝ f y c) =
        fderiv ℝ (fderiv ℝ f) y v w - fderiv ℝ f y c := by
  have hfd (z : E) (hz : z ∈ S) : HasFDerivAt f (fderiv ℝ f z) z :=
    ((hf.contDiffAt (hS.mem_nhds hz)).differentiableAt (by norm_num)).hasFDerivAt
  have hrd (z : E) (hz : z ∈ S) : HasFDerivAt r (fderiv ℝ r (f z)) (f z) :=
    ((hr.contDiffAt (hU.mem_nhds (hfU hz))).differentiableAt (by norm_num)).hasFDerivAt
  have hfirst (z : E) (hz : z ∈ S) :
      (fderiv ℝ r (f z)).comp (fderiv ℝ f z) = fderiv ℝ f z := by
    have heq : f =ᶠ[𝓝 z] r ∘ f := by
      filter_upwards [hS.mem_nhds hz] with x hx
      exact (hfix x hx).symm
    exact (((hrd z hz).comp z (hfd z hz)).congr_of_eventuallyEq heq).unique (hfd z hz)
  have happ (z : E) (hz : z ∈ S) (v : E) :
      fderiv ℝ r (f z) (fderiv ℝ f z v) = fderiv ℝ f z v :=
    congrArg (fun L : E →L[ℝ] F => L v) (hfirst z hz)
  refine ⟨happ y hy, ?_⟩
  intro v w c
  have hDDf : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) y) y :=
    (((hf.contDiffAt (hS.mem_nhds hy)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hDDr : HasFDerivAt (fderiv ℝ r) (fderiv ℝ (fderiv ℝ r) (f y)) (f y) :=
    (((hr.contDiffAt (hU.mem_nhds (hfU hy))).fderiv_right (m := 1)
      (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hw : HasFDerivAt (fun z => fderiv ℝ f z w)
      ((fderiv ℝ (fderiv ℝ f) y).flip w) y := by
    simpa only [ContinuousLinearMap.comp_zero, zero_add] using
      hDDf.clm_apply (hasFDerivAt_const w y)
  have heq : (fun z => fderiv ℝ f z w) =ᶠ[𝓝 y]
      (fun z => fderiv ℝ r (f z) (fderiv ℝ f z w)) := by
    filter_upwards [hS.mem_nhds hy] with z hz
    exact (happ z hz w).symm
  have hsecond := congrArg (fun L : E →L[ℝ] F => L v)
    ((((hDDr.comp y (hfd y hy)).clm_apply hw).congr_of_eventuallyEq heq).unique hw)
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, Function.comp_apply] at hsecond
  rw [add_comm] at hsecond
  rw [map_sub, happ y hy c, ← add_sub_assoc, hsecond]

end PoincareConjecture.M63
