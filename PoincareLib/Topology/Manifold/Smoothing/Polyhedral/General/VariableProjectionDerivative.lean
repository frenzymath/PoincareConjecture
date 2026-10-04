import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coordinates.StrictDerivativeCarrierChart
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# The derivative of a variable transverse projection at its center

Variation of the projection operator is multiplied by zero at
the center, so the derivative is the fixed projection there.
See Cairns 1940, pp. 804--806 and M76 derivation 71.
-/

set_option autoImplicit false

open scoped ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A smooth variable projection has strict derivative equal
to the fixed projection at its center. See Cairns pp. 804--806
and M76 derivation 71. -/
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
