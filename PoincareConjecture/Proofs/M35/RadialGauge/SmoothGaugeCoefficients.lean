import PoincareConjecture.Proofs.M35.RadialGauge.SmoothTargetCoupling

set_option autoImplicit false

open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

open SmoothRadial

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def smoothGaugeDrift (h xi : ℝ → ℝ) (x : E) : E :=
  (2 * axisDivision (deriv h) ‖x‖ - xi ‖x‖) • x

noncomputable def smoothGaugeForcing (h f₀ xi : ℝ → ℝ) (x : E) (sigma : ℝ) : ℝ :=
  2 * axisDivision (deriv h) ‖x‖ -
    2 * smoothEvenQuadratic (fun r => Real.exp (-2 * h r)) ‖x‖ -
    2 * Real.exp (2 * sigma) * targetQuadraticRemainder f₀ ‖Real.exp sigma • x‖ *
      Real.exp (-2 * h ‖x‖) - xi ‖x‖

theorem smoothGaugeDrift_contDiff {h xi : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (he : Function.Even h)
    (hxi : ContDiff ℝ ∞ xi) (hxie : Function.Even xi) :
    ContDiff ℝ ∞ (smoothGaugeDrift h xi : E → E) := by
  have hD : ContDiff ℝ ∞ (fun x : E => axisDivision (deriv h) ‖x‖) :=
    contDiff_even_norm (axisDivision_contDiff (contDiff_infty_iff_deriv.mp hh).2)
      (axisDivision_deriv_even hh he)
  exact ((contDiff_const.mul hD).sub (contDiff_even_norm hxi hxie)).smul contDiff_id

theorem smoothGaugeForcing_contDiff {h f₀ xi : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (he : Function.Even h)
    (hf : ContDiff ℝ ∞ f₀) (hfo : Function.Odd f₀)
    (hxi : ContDiff ℝ ∞ xi) (hxie : Function.Even xi) :
    ContDiff ℝ ∞ (fun p : E × ℝ => smoothGaugeForcing h f₀ xi p.1 p.2) := by
  have hD : ContDiff ℝ ∞ (fun x : E => axisDivision (deriv h) ‖x‖) :=
    contDiff_even_norm (axisDivision_contDiff (contDiff_infty_iff_deriv.mp hh).2)
      (axisDivision_deriv_even hh he)
  have hExp : ContDiff ℝ ∞ (fun r => Real.exp (-2 * h r)) :=
    (contDiff_const.mul hh).exp
  have hExpe : Function.Even (fun r => Real.exp (-2 * h r)) :=
    fun r => congrArg (fun z => Real.exp (-2 * z)) (he r)
  have hQ := smoothEvenQuadratic_contDiff_norm (E := E) hExp hExpe
  have htarget : ContDiff ℝ ∞ (fun x : E => targetQuadraticRemainder f₀ ‖x‖) :=
    contDiff_even_norm (targetQuadraticRemainder_contDiff hf) (targetQuadraticRemainder_even hf hfo)
  have hscaled : ContDiff ℝ ∞ (fun p : E × ℝ =>
      targetQuadraticRemainder f₀ ‖Real.exp p.2 • p.1‖) :=
    htarget.comp (contDiff_snd.exp.smul contDiff_fst)
  have hfactor : ContDiff ℝ ∞ (fun p : E × ℝ => Real.exp (2 * p.2)) :=
    (contDiff_const.mul contDiff_snd).exp
  have hcurrent : ContDiff ℝ ∞ (fun p : E × ℝ => Real.exp (-2 * h ‖p.1‖)) :=
    (contDiff_even_norm (E := E) hExp hExpe).comp contDiff_fst
  exact (((contDiff_const.mul (hD.comp contDiff_fst)).sub
      (contDiff_const.mul (hQ.comp contDiff_fst))).sub
      (((contDiff_const.mul hfactor).mul hscaled).mul hcurrent)).sub
    ((contDiff_even_norm hxi hxie).comp contDiff_fst)

theorem smoothGaugeDrift_equivariant (h xi : ℝ → ℝ) (Q : E ≃ₗᵢ[ℝ] E) (x : E) :
    smoothGaugeDrift h xi (Q x) = Q (smoothGaugeDrift h xi x) := by
  simp only [smoothGaugeDrift, Q.norm_map, map_smul]

theorem smoothGaugeForcing_invariant (h f₀ xi : ℝ → ℝ)
    (Q : E ≃ₗᵢ[ℝ] E) (x : E) (sigma : ℝ) :
    smoothGaugeForcing h f₀ xi (Q x) sigma = smoothGaugeForcing h f₀ xi x sigma := by
  simp only [smoothGaugeForcing, Q.norm_map, norm_smul, Real.norm_eq_abs, Real.abs_exp]

end PoincareConjecture.M35.RadialGauge
