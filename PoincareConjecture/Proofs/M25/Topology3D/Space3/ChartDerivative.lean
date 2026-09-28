import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Topology.OpenPartialHomeomorph.Basic











set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M25.Topology3D

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]



theorem smoothChart_symm_fderiv_comp (e : OpenPartialHomeomorph E F)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    {x : E} (hx : x ∈ e.source) :
    (fderiv ℝ e.symm (e x)).comp (fderiv ℝ e x) = ContinuousLinearMap.id ℝ E := by
  have hd := (he.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt (by simp)
  have hid := (hi.contDiffAt (e.open_target.mem_nhds (e.map_source hx))).differentiableAt
    (by simp)
  have hcomp := hid.hasFDerivAt.comp x hd.hasFDerivAt
  have heq : (fun y => e.symm (e y)) =ᶠ[𝓝 x] (fun y => y) :=
    e.eventually_left_inverse hx
  exact (hcomp.congr_of_eventuallyEq heq.symm).unique (hasFDerivAt_id x)



theorem exists_smoothChart_derivative (e : OpenPartialHomeomorph E F)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    {x : E} (hx : x ∈ e.source) :
    ∃ A : E ≃L[ℝ] F, HasFDerivAt e (A : E →L[ℝ] F) x := by
  have hleft := smoothChart_symm_fderiv_comp e he hi hx
  have hright := smoothChart_symm_fderiv_comp e.symm hi he (e.map_source hx)
  rw [e.left_inv hx] at hright
  let A := ContinuousLinearEquiv.equivOfInverse'
    (fderiv ℝ e x) (fderiv ℝ e.symm (e x)) hright hleft
  exact ⟨A, ((he.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt
    (by simp)).hasFDerivAt⟩

end PoincareConjecture.M25.Topology3D
