import PoincareConjecture.Proofs.M76.Mathlib.StrictDerivativeCarrierChart
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

set_option autoImplicit false

open scoped ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem ContDiffAt.hasStrictFDerivAt_variable_projection
    {Q : E → E →L[ℝ] F} {a : E} (hQ : ContDiffAt ℝ ∞ Q a) :
    HasStrictFDerivAt (fun y => Q y (y - a)) (Q a) a := by
  have hd := (hQ.differentiableAt (by simp)).hasFDerivAt.clm_apply
    ((hasFDerivAt_id a).sub_const a)
  have hderiv : HasFDerivAt (fun y => Q y (y - a)) (Q a) a := by
    convert! hd using 1
    ext v
    simp
  exact (hQ.clm_apply (contDiffAt_id.sub contDiffAt_const)).hasStrictFDerivAt' hderiv (by simp)
