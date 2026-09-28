import PoincareConjecture.Proofs.M65.Mathlib.Plateau.BeltramiSmoothForcing
import Mathlib.Analysis.SpecialFunctions.ExpDeriv











set_option autoImplicit false

noncomputable section

open MeasureTheory FourierTransform Filter LineDeriv
open scoped Topology SchwartzMap ContDiff ComplexConjugate LineDeriv

namespace Complex






theorem exists_smooth_beltrami_logPotential (μ : 𝓢(ℂ, ℂ))
    (hμ : HasCompactSupport (μ : ℂ → ℂ)) {k : ℝ} (hk : k < 1)
    (hbound : ∀ z, ‖μ z‖ ≤ k) :
    ∃ q : ℂ → ℂ, ContDiff ℝ ∞ q ∧ Tendsto q (cocompact ℂ) (𝓝 0) ∧
      ∀ z, (fderiv ℝ q z 1 + I * fderiv ℝ q z I) / 2 -
        μ z * ((fderiv ℝ q z 1 - I * fderiv ℝ q z I) / 2) =
          (fderiv ℝ (μ : ℂ → ℂ) z 1 - I * fderiv ℝ (μ : ℂ → ℂ) z I) / 2 := by
  let a : 𝓢(ℂ, ℂ) := (2⁻¹ : ℂ) • (∂_{(1 : ℂ)} μ - I • ∂_{I} μ)
  have hμ1 : HasCompactSupport ((∂_{(1 : ℂ)} μ : 𝓢(ℂ, ℂ)) : ℂ → ℂ) :=
    hμ.fderiv_apply (𝕜 := ℝ) 1
  have hμI : HasCompactSupport ((∂_{I} μ : 𝓢(ℂ, ℂ)) : ℂ → ℂ) :=
    hμ.fderiv_apply (𝕜 := ℝ) I
  have ha : HasCompactSupport (a : ℂ → ℂ) :=
    (hμ1.sub hμI.mul_left).mul_left
  obtain ⟨h, _, heq⟩ := exists_schwartz_beltrami_forcing μ hμ hk hbound a ha
  refine ⟨schwartzDbarPotential h, contDiff_schwartzDbarPotential h,
    tendsto_schwartzDbarPotential h, fun z => ?_⟩
  rw [dbar_schwartzDbarPotential, dz_schwartzDbarPotential]
  change h z - μ z * beurlingSchwartz h z = _
  rw [heq z]
  simp only [a, smul_apply, sub_apply, smul_eq_mul,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  ring

private theorem fderiv_exp_comp (q : ℂ → ℂ) (hq : ContDiff ℝ ∞ q) (z v : ℂ) :
    fderiv ℝ (fun y => exp (q y)) z v = exp (q z) * fderiv ℝ q z v := by
  rw [((hq.differentiable (by norm_num)).differentiableAt.hasFDerivAt.cexp).fderiv]
  rfl





theorem exists_smooth_beltrami_closed_coefficients (μ : 𝓢(ℂ, ℂ))
    (hμ : HasCompactSupport (μ : ℂ → ℂ)) {k : ℝ} (hk : k < 1)
    (hbound : ∀ z, ‖μ z‖ ≤ k) :
    ∃ w : ℂ → ℂ, ContDiff ℝ ∞ w ∧ Tendsto w (cocompact ℂ) (𝓝 1) ∧
      (∀ z, w z ≠ 0) ∧ ∀ z,
        fderiv ℝ w z 1 + I * fderiv ℝ w z I =
          fderiv ℝ (fun y => μ y * w y) z 1 -
            I * fderiv ℝ (fun y => μ y * w y) z I := by
  obtain ⟨q, hq, hqinf, hqeq⟩ := exists_smooth_beltrami_logPotential μ hμ hk hbound
  refine ⟨fun z => exp (q z), hq.cexp, ?_, fun z => exp_ne_zero _, fun z => ?_⟩
  · simpa only [exp_zero, Function.comp_def] using! (continuous_exp.tendsto 0).comp hqinf
  · rw [fderiv_fun_mul μ.differentiableAt
      ((hq.cexp.differentiable (by norm_num)).differentiableAt)]
    simp only [add_apply, smul_apply, smul_eq_mul, fderiv_exp_comp q hq]
    have heq := congrArg (fun u : ℂ => 2 * exp (q z) * u) (hqeq z)
    linear_combination heq

end Complex
