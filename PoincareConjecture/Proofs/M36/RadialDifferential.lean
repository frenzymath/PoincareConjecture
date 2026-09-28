import PoincareConjecture.Proofs.M36.RadialMetric
import PoincareConjecture.Proofs.M36.RadialArclength
import PoincareConjecture.Proofs.M36.MetricPathLength
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false

open scoped Manifold ContDiff Bundle RealInnerProductSpace

namespace PoincareConjecture.M36

theorem radial_metric_quadratic_lower (g₀ : StandardInitialMetric)
    (x : StandardCapSpace) (hx : x ≠ 0) (v : StandardCapSpace) :
    axisRadialCoefficient g₀ ‖x‖ * (inner ℝ (‖x‖⁻¹ • x) v) ^ 2 ≤
      g₀.metric.inner x v v := by
  have hu : ‖‖x‖⁻¹ • x‖ = 1 := by simp [norm_smul, norm_ne_zero_iff.mpr hx]
  have hc := real_inner_mul_inner_self_le (‖x‖⁻¹ • x) v
  rw [real_inner_self_eq_norm_sq, hu, one_pow, one_mul] at hc
  have hnonneg := mul_nonneg (axisTangentialCoefficient_pos g₀ ‖x‖).le
    (sub_nonneg.mpr hc)
  rw [standard_metric_radial_formula g₀ x hx v v]
  nlinarith

theorem radial_differential_le_tangentNorm (g₀ : StandardInitialMetric)
    (x : StandardCapSpace) (hx : x ≠ 0) (v : StandardCapSpace) :
    |radialSpeed g₀ ‖x‖ * inner ℝ (‖x‖⁻¹ • x) v| ≤ g₀.metric.tangentNorm x v := by
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sq_abs, mul_pow, radialSpeed, Real.sq_sqrt (axisRadialCoefficient_pos g₀ ‖x‖).le]
  change axisRadialCoefficient g₀ ‖x‖ * _ ≤ (Real.sqrt (g₀.metric.inner x v v)) ^ 2
  rw [Real.sq_sqrt (metric_inner_nonneg g₀.metric x v)]
  exact radial_metric_quadratic_lower g₀ x hx v

theorem norm_path_hasDerivAt {gamma : ℝ → StandardCapSpace} {v : StandardCapSpace}
    {t : ℝ} (hgamma : HasDerivAt gamma v t) (hne : gamma t ≠ 0) :
    HasDerivAt (fun s => ‖gamma s‖) (inner ℝ (‖gamma t‖⁻¹ • gamma t) v) t := by
  have h := hgamma.norm_sq.sqrt (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))
  simp only [Real.sqrt_sq (norm_nonneg _)] at h
  convert! h using 1
  rw [real_inner_smul_left]
  field_simp

theorem radial_path_hasDerivAt (g₀ : StandardInitialMetric)
    {gamma : ℝ → StandardCapSpace} {v : StandardCapSpace} {t : ℝ}
    (hgamma : HasDerivAt gamma v t) (hne : gamma t ≠ 0) :
    HasDerivAt (fun s => radialArclength g₀ ‖gamma s‖)
      (radialSpeed g₀ ‖gamma t‖ * inner ℝ (‖gamma t‖⁻¹ • gamma t) v) t := by
  simpa only [Function.comp_def] using
    (radialArclength_hasDerivAt g₀ ‖gamma t‖).comp t (norm_path_hasDerivAt hgamma hne)

theorem radial_path_deriv_bound (g₀ : StandardInitialMetric)
    {gamma : ℝ → StandardCapSpace} {t : ℝ}
    (hgamma : DifferentiableAt ℝ gamma t) (hne : gamma t ≠ 0) :
    ‖deriv (fun s => radialArclength g₀ ‖gamma s‖) t‖ ≤
      metricPathSpeed g₀.metric gamma t := by
  rw [(radial_path_hasDerivAt g₀ hgamma.hasDerivAt hne).deriv, Real.norm_eq_abs]
  change _ ≤ g₀.metric.tangentNorm (gamma t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) gamma t 1)
  rw [mfderiv_eq_fderiv]
  exact radial_differential_le_tangentNorm g₀ (gamma t) hne (deriv gamma t)

end PoincareConjecture.M36
