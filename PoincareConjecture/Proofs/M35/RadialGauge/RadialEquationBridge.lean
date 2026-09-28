import PoincareConjecture.Proofs.M35.RadialGauge.RadialProfileCalculus

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped ContDiff RealInnerProductSpace

namespace PoincareConjecture.M35.RadialGauge

local notation "V" => EuclideanSpace ℝ (Fin 5)

theorem R5_radial_source_operator
    {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) {x : V} (hx : x ≠ 0)
    {b : V → V} {G : V → ℝ → ℝ} {d : ℝ}
    (hb : b x = (d / ‖x‖) • x) :
    euclideanLaplacian (fun y : V => w ‖y‖) x +
      gaugeSource b G (fun y => w ‖y‖) x =
      deriv (deriv w) ‖x‖ + (4 / ‖x‖ + d) * deriv w ‖x‖ +
        deriv w ‖x‖ ^ 2 + G x (w ‖x‖) := by
  have hd := radialProfile_hasFDerivAt (hw.differentiable (by simp) ‖x‖) hx
  have hn := radialProfile_fderiv_norm (hw.differentiable (by simp) ‖x‖) hx
  rw [radialProfile_euclideanLaplacian hw hx]
  change deriv (deriv w) ‖x‖ + (4 : ℝ) * deriv w ‖x‖ / ‖x‖ +
    (fderiv ℝ (fun y : V => w ‖y‖) x (b x) +
      ‖fderiv ℝ (fun y : V => w ‖y‖) x‖ ^ 2 + G x (w ‖x‖)) = _
  rw [hn, sq_abs, hd.fderiv, hb]
  simp only [smul_apply, innerSL_apply_apply, inner_smul_right,
    real_inner_self_eq_norm_sq, smul_eq_mul]
  field_simp [norm_ne_zero_iff.mpr hx]
  ring

theorem R5_operator_eq_corrected_logarithmic
    {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) {x : V} (hx : x ≠ 0)
    (f f₀ velocity : ℝ → ℝ) {b : V → V} {G : V → ℝ → ℝ}
    (hb : b x = ((2 * deriv f ‖x‖ / f ‖x‖ - 2 / ‖x‖ - velocity ‖x‖) / ‖x‖) • x)
    (hG : G x (w ‖x‖) =
      2 * deriv f ‖x‖ / (‖x‖ * f ‖x‖) -
      2 * f₀ (mapRadius w ‖x‖) * deriv f₀ (mapRadius w ‖x‖) /
        (mapRadius w ‖x‖ * f ‖x‖ ^ 2) - velocity ‖x‖ / ‖x‖) :
    euclideanLaplacian (fun y : V => w ‖y‖) x +
      gaugeSource b G (fun y => w ‖y‖) x =
        logarithmicRadialOperator 3 f f₀ velocity w ‖x‖ := by
  rw [R5_radial_source_operator hw hx hb, hG, logarithmicRadialOperator]
  norm_num only [show (3 : ℝ) - 1 = 2 by norm_num]
  ring

theorem invariant_R5_operator_eq_corrected_logarithmic
    {u : V → ℝ} (hu : ContDiff ℝ ∞ u)
    (hinvariant : ∀ (L : V ≃ₗᵢ[ℝ] V) x, u (L x) = u x)
    {e : V} (he : ‖e‖ = 1) {x : V} (hx : x ≠ 0)
    (f f₀ velocity : ℝ → ℝ) {b : V → V} {G : V → ℝ → ℝ}
    (hb : b x = ((2 * deriv f ‖x‖ / f ‖x‖ - 2 / ‖x‖ - velocity ‖x‖) / ‖x‖) • x)
    (hG : G x (u x) =
      2 * deriv f ‖x‖ / (‖x‖ * f ‖x‖) -
      2 * f₀ (mapRadius (fun r => u (r • e)) ‖x‖) *
        deriv f₀ (mapRadius (fun r => u (r • e)) ‖x‖) /
        (mapRadius (fun r => u (r • e)) ‖x‖ * f ‖x‖ ^ 2) - velocity ‖x‖ / ‖x‖) :
    euclideanLaplacian u x + gaugeSource b G u x =
      logarithmicRadialOperator 3 f f₀ velocity (fun r => u (r • e)) ‖x‖ := by
  have hw : ContDiff ℝ ∞ (fun r : ℝ => u (r • e)) :=
    hu.comp (contDiff_id.smul contDiff_const)
  have heq := orthogonal_invariant_radial_trace hinvariant he
  calc
    _ = euclideanLaplacian (fun y : V => u (‖y‖ • e)) x +
        gaugeSource b G (fun y => u (‖y‖ • e)) x :=
      congrArg (fun v : V → ℝ => euclideanLaplacian v x + gaugeSource b G v x) heq
    _ = _ := R5_operator_eq_corrected_logarithmic hw hx f f₀ velocity hb
      (by rwa [← congrFun heq x])

end PoincareConjecture.M35.RadialGauge
