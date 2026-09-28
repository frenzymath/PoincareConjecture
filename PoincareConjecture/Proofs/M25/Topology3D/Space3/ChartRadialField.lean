import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.OpenPartialHomeomorph.Basic











set_option autoImplicit false

open Set
open scoped ContDiff

namespace PoincareConjecture.M25.Topology3D

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]



noncomputable def chartRadialField (e : OpenPartialHomeomorph E F) (y : F) : F :=
  -((fderiv ℝ e (e.symm y)) (e.symm y))



theorem chartRadialField_contDiffOn (e : OpenPartialHomeomorph E F)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target) :
    ContDiffOn ℝ ∞ (chartRadialField e) e.target := by
  exact (((he.fderiv_of_isOpen e.open_source (by simp)).comp hi
    (fun _ hy => e.map_target hy)).clm_apply hi).neg



theorem chartRadialField_track_hasDerivAt (e : OpenPartialHomeomorph E F)
    (he : ContDiffOn ℝ ∞ e e.source) (x : E) (t : ℝ)
    (hx : Real.exp (-t) • x ∈ e.source) :
    HasDerivAt (fun s : ℝ => e (Real.exp (-s) • x))
      (chartRadialField e (e (Real.exp (-t) • x))) t := by
  have hs : HasDerivAt (fun s : ℝ => Real.exp (-s) • x)
      (-(Real.exp (-t) • x)) t := by
    simpa only [Pi.neg_apply, id_eq, mul_neg_one, neg_smul] using
      ((hasDerivAt_id t).neg.exp).smul_const x
  have hd := ((he.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt t hs
  simpa only [Function.comp_def, chartRadialField, e.left_inv hx, map_neg] using hd

end PoincareConjecture.M25.Topology3D
