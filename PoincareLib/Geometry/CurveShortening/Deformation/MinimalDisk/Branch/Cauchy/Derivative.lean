import PoincareLib.Geometry.CurveShortening.Deformation.MinimalDisk.Branch.Cauchy.Inverse
import PoincareLib.Geometry.CurveShortening.Deformation.MinimalDisk.Branch.Cauchy.Bound

/-!
# The actual Cauchy derivative bound

Actual derivative commutation and the genuine compact-support integral
estimate control the full real derivative. Source: Eschenburg--Tribuzy,
Conformal mappings of surfaces and Cauchy--Riemann inequalities,
preprint pp. 8--11; M65 derivation 32, seventh consumer,
for MT Lemma 19.2, printed pp. 438--439.
-/

set_option autoImplicit false

open Set Metric
open scoped Topology ContDiff

namespace PoincareMT.M65Branch

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The norm of the actual real derivative of the Cauchy integral is
bounded by the genuine derivative of its compact forcing. Source:
Eschenburg--Tribuzy, preprint pp. 8--11; derivation 32, seventh consumer. -/
theorem norm_fderiv_cauchyOperator_le {h : ℂ → E} {R B : ℝ}
    (hR : 0 < R) (hB : 0 ≤ B) (hh : ContDiff ℝ 1 h)
    (hsupport : tsupport h ⊆ closedBall (0 : ℂ) R)
    (hbound : ∀ w ∈ closedBall (0 : ℂ) R, ‖fderiv ℝ h w‖ ≤ B) (z : ℂ) :
    ‖fderiv ℝ (cauchyOperator h) z‖ ≤ 8 * R * B := by
  have hs : HasCompactSupport h :=
    (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset isClosed_closure hsupport
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [fderiv_cauchyOperator_apply hh hs]
  have hvsupport : Function.support (fun w => fderiv ℝ h w v) ⊆
      closedBall (0 : ℂ) R :=
    (subset_tsupport _).trans ((tsupport_fderiv_apply_subset ℝ v).trans hsupport)
  have hvbound (w : ℂ) (hw : w ∈ closedBall (0 : ℂ) R) :
      ‖fderiv ℝ h w v‖ ≤ B * ‖v‖ :=
    ((fderiv ℝ h w).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hbound w hw) (norm_nonneg v))
  exact (norm_cauchyOperator_le hR (mul_nonneg hB (norm_nonneg v))
    ((hh.continuous_fderiv one_ne_zero).clm_apply continuous_const)
    hvsupport hvbound z).trans_eq (by ring)

end PoincareMT.M65Branch
