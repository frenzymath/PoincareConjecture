import PoincareConjecture.Proofs.M35.RadialGauge.GaugeEquation
import PoincareConjecture.Proofs.M35.RadialGauge.RadialEquationBridge










set_option autoImplicit false

open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

local notation "V" => EuclideanSpace ℝ (Fin 5)



theorem invariant_R5_time_equation
    {u : ℝ → V → ℝ} {b : V → V} {G : V → ℝ → ℝ} {t r : ℝ}
    (hu : ContDiff ℝ ∞ (u t))
    (hinvariant : ∀ (L : V ≃ₗᵢ[ℝ] V) x, u t (L x) = u t x)
    {e : V} (he : ‖e‖ = 1) (hr : 0 < r)
    (f f₀ velocity : ℝ → ℝ)
    (hb : b (r • e) = ((2 * deriv f r / f r - 2 / r - velocity r) / r) • (r • e))
    (hG : G (r • e) (u t (r • e)) =
      2 * deriv f r / (r * f r) -
      2 * f₀ (mapRadius (fun s => u t (s • e)) r) *
        deriv f₀ (mapRadius (fun s => u t (s • e)) r) /
        (mapRadius (fun s => u t (s • e)) r * f r ^ 2) - velocity r / r)
    (hPDE : HasDerivAt (fun s => u s (r • e))
      (euclideanLaplacian (u t) (r • e) + gaugeSource b G (u t) (r • e)) t) :
    HasDerivAt (fun s => u s (r • e))
      (logarithmicRadialOperator 3 f f₀ velocity (fun s => u t (s • e)) r) t := by
  have hnorm : ‖r • e‖ = r := by
    rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos hr]
  have hx : r • e ≠ 0 := by
    intro hx
    have hzero := congrArg norm hx
    rw [hnorm, norm_zero] at hzero
    exact hr.ne' hzero
  have hoperator := invariant_R5_operator_eq_corrected_logarithmic hu hinvariant he hx
    f f₀ velocity (by simpa only [hnorm] using hb) (by simpa only [hnorm] using hG)
  rw [hnorm] at hoperator
  exact hPDE.congr_deriv hoperator




theorem invariant_R5_radius_time_equation
    {u : ℝ → V → ℝ} {b : V → V} {G : V → ℝ → ℝ} {t r : ℝ}
    (hu : ContDiff ℝ ∞ (u t))
    (hinvariant : ∀ (L : V ≃ₗᵢ[ℝ] V) x, u t (L x) = u t x)
    {e : V} (he : ‖e‖ = 1) (hr : 0 < r)
    (f f₀ velocity : ℝ → ℝ) (hf : f r ≠ 0)
    (hb : b (r • e) = ((2 * deriv f r / f r - 2 / r - velocity r) / r) • (r • e))
    (hG : G (r • e) (u t (r • e)) =
      2 * deriv f r / (r * f r) -
      2 * f₀ (mapRadius (fun s => u t (s • e)) r) *
        deriv f₀ (mapRadius (fun s => u t (s • e)) r) /
        (mapRadius (fun s => u t (s • e)) r * f r ^ 2) - velocity r / r)
    (hPDE : HasDerivAt (fun s => u s (r • e))
      (euclideanLaplacian (u t) (r • e) + gaugeSource b G (u t) (r • e)) t) :
    HasDerivAt (fun s => mapRadius (fun z => u s (z • e)) r)
      (harmonicRadialOperator 3 f f₀ velocity (mapRadius (fun z => u t (z • e))) r) t := by
  have hlog := invariant_R5_time_equation hu hinvariant he hr f f₀ velocity hb hG hPDE
  have hs : ContDiff ℝ ∞ (fun s : ℝ => u t (s • e)) :=
    hu.comp (contDiff_id.smul contDiff_const)
  rw [harmonicRadialOperator_mapRadius 3 f f₀ velocity hs hr hf]
  exact mapRadius_hasDerivAt_time r hlog

end PoincareConjecture.M35.RadialGauge
