import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

namespace Poincare.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem fderiv_fderiv_le_of_concaveOn_sub_norm_sq
    {f : E → ℝ} {U : Set E} {C : ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U)
    (hconc : ConcaveOn ℝ U (fun y => f y - C * ‖y‖ ^ 2 / 2))
    {x : E} (hx : x ∈ U) (v : E) :
    fderiv ℝ (fderiv ℝ f) x v v ≤ C * ‖v‖ ^ 2 := by
  let A : ℝ → E := fun t => x + t • v
  let q : ℝ → ℝ := fun t => f (A t) - C * ‖A t‖ ^ 2 / 2
  let q' : ℝ → ℝ := fun t => fderiv ℝ f (A t) v - C * inner ℝ (A t) v
  have hA (t : ℝ) : HasDerivAt A v t := by
    simpa [A] using ((hasDerivAt_id t).smul_const v).const_add x
  have hAo : IsOpen (A ⁻¹' U) := hU.preimage (by fun_prop)
  have hA0 : (0 : ℝ) ∈ A ⁻¹' U := by simpa [A] using hx
  have hq : ConcaveOn ℝ (A ⁻¹' U) q := by
    simpa [A, q, Function.comp_def, AffineMap.coe_lineMap, add_comm] using
      hconc.comp_affineMap (AffineMap.lineMap x (x + v))
  have hd (t : ℝ) (ht : t ∈ A ⁻¹' U) : HasDerivAt q (q' t) t := by
    have hft := (hf.contDiffAt (hU.mem_nhds ht)).differentiableAt (by simp)
    change HasDerivAt (fun t => f (A t) - C * ‖A t‖ ^ 2 / 2)
      (fderiv ℝ f (A t) v - C * inner ℝ (A t) v) t
    convert (hft.hasFDerivAt.comp_hasDerivAt t (hA t)).sub
      (((hA t).norm_sq.const_mul C).div_const 2) using 1 <;> first | rfl | ring
  have hant : AntitoneOn (deriv q) (A ⁻¹' U) :=
    hq.antitoneOn_deriv (fun t ht => (hd t ht).differentiableAt)
  have hn : deriv (deriv q) 0 ≤ 0 := by
    rw [← derivWithin_of_mem_nhds (hAo.mem_nhds hA0)]
    exact hant.derivWithin_nonpos
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_of_isOpen hU (m := ∞) (by simp)).contDiffAt
      (hU.mem_nhds hx)).differentiableAt (by simp)
  have hlinear : HasDerivAt (fun t => fderiv ℝ f (A t) v)
      (fderiv ℝ (fderiv ℝ f) x v v) 0 := by
    have hfd' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) (A 0) := by
      simpa [A] using hfd.hasFDerivAt
    have h := (hfd'.comp_hasDerivAt 0 (hA 0)).clm_apply (hasDerivAt_const 0 v)
    simpa [A] using h
  have hinner : HasDerivAt (fun t => inner ℝ (A t) v) (‖v‖ ^ 2) 0 := by
    simpa using (hA 0).inner ℝ (hasDerivAt_const 0 v)
  have hsecond : HasDerivAt (deriv q)
      (fderiv ℝ (fderiv ℝ f) x v v - C * ‖v‖ ^ 2) 0 := by
    apply (hlinear.sub (hinner.const_mul C)).congr_of_eventuallyEq
    filter_upwards [hAo.mem_nhds hA0] with t ht
    exact (hd t ht).deriv
  rw [hsecond.deriv] at hn
  linarith

end Poincare.Analysis
