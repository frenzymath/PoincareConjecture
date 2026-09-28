import PoincareConjecture.Proofs.M36.RadialDifferential









set_option autoImplicit false

open scoped RealInnerProductSpace

namespace PoincareConjecture.M36

theorem unit_velocity_of_radial_derivative_one (g₀ : StandardInitialMetric)
    {x v : StandardCapSpace} (hx : x ≠ 0)
    (hmetric : g₀.metric.inner x v v = 1)
    (hradial : radialSpeed g₀ ‖x‖ * inner ℝ (‖x‖⁻¹ • x) v = 1) :
    v = (radialSpeed g₀ ‖x‖)⁻¹ • (‖x‖⁻¹ • x) := by
  let u := ‖x‖⁻¹ • x
  let alpha := inner ℝ u v
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, norm_ne_zero_iff.mpr hx]
  have huu : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  have hvu : inner ℝ v u = alpha := (real_inner_comm v u).symm
  have hresidual : inner ℝ (v - alpha • u) (v - alpha • u) =
      inner ℝ v v - alpha ^ 2 := by
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, huu, mul_one, hvu]
    dsimp only [alpha]
    ring
  have hspeedSq : (radialSpeed g₀ ‖x‖) ^ 2 = axisRadialCoefficient g₀ ‖x‖ :=
    Real.sq_sqrt (axisRadialCoefficient_pos g₀ ‖x‖).le
  have hradialSq : axisRadialCoefficient g₀ ‖x‖ * alpha ^ 2 = 1 := by
    have h := congrArg (fun s : ℝ => s ^ 2) hradial
    simpa only [mul_pow, hspeedSq, one_pow] using h
  have hformula := standard_metric_radial_formula g₀ x hx v v
  have hzero : axisTangentialCoefficient g₀ ‖x‖ *
      inner ℝ (v - alpha • u) (v - alpha • u) = 0 := by
    rw [hresidual]
    change g₀.metric.inner x v v = axisTangentialCoefficient g₀ ‖x‖ * inner ℝ v v +
      (axisRadialCoefficient g₀ ‖x‖ - axisTangentialCoefficient g₀ ‖x‖) * alpha * alpha
      at hformula
    nlinarith
  have hw : v - alpha • u = 0 := inner_self_eq_zero.mp
    ((mul_eq_zero.mp hzero).resolve_left (axisTangentialCoefficient_pos g₀ ‖x‖).ne')
  have halpha : alpha = (radialSpeed g₀ ‖x‖)⁻¹ := by
    apply mul_left_cancel₀ (radialSpeed_pos g₀ ‖x‖).ne'
    rw [mul_inv_cancel₀ (radialSpeed_pos g₀ ‖x‖).ne']
    exact hradial
  simpa only [halpha] using sub_eq_zero.mp hw

end PoincareConjecture.M36
