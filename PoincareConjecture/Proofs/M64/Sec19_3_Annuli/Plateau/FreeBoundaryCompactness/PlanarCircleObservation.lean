import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.ObservationWithCurrent
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.CircleCurrentLimit
import PoincareConjecture.Definitions.M64Annulus
import PoincareConjecture.Proofs.M58.Cor18_28_PolarDerivatives
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64

open Proofs.M58

def planarCircleObservation {circumference : ℝ} (q : AddCircle circumference) : LoopPlane :=
  !₂[(AddCircle.toCircle q : ℂ).re, (AddCircle.toCircle q : ℂ).im]

theorem planarCircleObservation_quotient {circumference : ℝ}
    (C : M62.CircleGeometry circumference) (x : ℝ) :
    planarCircleObservation (C.quotient x) = angularPoint (curvePeriod / circumference * x) := by
  ext i
  fin_cases i <;>
    simp only [planarCircleObservation, M62.CircleGeometry.quotient,
      AddCircle.toCircle_apply_mk, Circle.coe_exp, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, angularPoint, curvePeriod]

theorem planarCircleObservation_norm {circumference : ℝ}
    (C : M62.CircleGeometry circumference) (q : C.Point) :
    ‖planarCircleObservation q‖ = 1 := by
  induction q using QuotientAddGroup.induction_on with
  | H x =>
    rw [show planarCircleObservation (x : AddCircle circumference) =
      angularPoint (curvePeriod / circumference * x) from planarCircleObservation_quotient C x]
    exact norm_angularPoint _

theorem planarCircleObservation_contMDiff {circumference : ℝ}
    (C : M62.CircleGeometry circumference) :
    let := C.chartedSpace
    ContMDiff (𝓡 1) (𝓡 2) ∞ (@planarCircleObservation circumference) := by
  let := C.chartedSpace
  change ContMDiff (𝓡 1) (𝓡 2) ∞ (@planarCircleObservation circumference)
  intro q
  induction q using QuotientAddGroup.induction_on with
  | H x =>
    let hloc := C.quotient_local_diffeomorph x
    have hformula : planarCircleObservation =ᶠ[𝓝 (C.quotient x)]
        (fun q => angularPoint (curvePeriod / circumference * hloc.localInverse q)) := by
      filter_upwards [hloc.localInverse_eventuallyEq_right] with q hq
      change C.quotient (hloc.localInverse q) = q at hq
      exact (congrArg planarCircleObservation hq).symm.trans
        (planarCircleObservation_quotient C _)
    have hangle : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞
        (fun y : ℝ => angularPoint (curvePeriod / circumference * y)) :=
      (contDiff_angularPoint.comp (contDiff_const.mul contDiff_id)).contMDiff
    exact (hangle.contMDiffAt.comp _ hloc.localInverse_contMDiffAt).congr_of_eventuallyEq hformula

theorem planarCircleCurrent_angularPoint (x d : ℝ) :
    planarCircleCurrent (angularPoint x) (d • angularVector x) = d := by
  have htrig := Real.sin_sq_add_cos_sq x
  simp only [planarCircleCurrent, angularPoint, angularVector,
    PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
  calc
    _ = d * (Real.sin x ^ 2 + Real.cos x ^ 2) := by ring
    _ = d := by rw [htrig, mul_one]

theorem planarCircleCurrent_phase_derivative {circumference : ℝ}
    (C : M62.CircleGeometry circumference) (L : LoopPlane → ℝ)
    {p : LoopPlane} (hL : DifferentiableAt ℝ L p) (v : LoopPlane) :
    planarCircleCurrent (planarCircleObservation (C.quotient (L p)))
      (fderiv ℝ (fun q => planarCircleObservation (C.quotient (L q))) p v) =
        (curvePeriod / circumference) * fderiv ℝ L p v := by
  have heq : (fun q => planarCircleObservation (C.quotient (L q))) =
      fun q => angularPoint (curvePeriod / circumference * L q) :=
    funext fun q => planarCircleObservation_quotient C (L q)
  have hd := (hasDerivAt_angularPoint (curvePeriod / circumference * L p)).hasFDerivAt.comp p
    (hL.hasFDerivAt.const_mul (curvePeriod / circumference))
  simp only [Function.comp_def] at hd
  rw [heq, hd.fderiv, planarCircleObservation_quotient]
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    smul_apply, smul_eq_mul] using
      planarCircleCurrent_angularPoint (curvePeriod / circumference * L p)
        ((curvePeriod / circumference) * fderiv ℝ L p v)

end PoincareConjecture.M64
