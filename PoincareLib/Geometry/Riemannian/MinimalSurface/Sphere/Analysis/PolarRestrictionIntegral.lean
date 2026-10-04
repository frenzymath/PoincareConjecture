import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Analysis.Complex.CauchyRiemann.Polar
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Integrating derivatives of polar restrictions

The Cauchy right inverse in the local branch-isolation proof uses the
fundamental theorem of calculus along radii and circles. These identities
hold for actual C1 maps into real Banach spaces. Source: the local-frame
derivation of Sacks-Uhlenbeck Theorem 1.6, printed p. 5.
-/

set_option autoImplicit false

open Complex MeasureTheory
open scoped Topology ContDiff

namespace PoincareMT.M60

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

private theorem continuous_polar_differential {f : ℂ → V}
    (hf : ContDiff ℝ 1 f) (z : ℂ) :
    Continuous (fun p : ℝ × ℝ => fderiv ℝ f (z - circleMap 0 p.1 p.2)) := by
  apply (hf.continuous_fderiv (by simp)).comp
  simp only [circleMap_zero]
  fun_prop

/-- The radial derivative varies continuously over the full polar
rectangle, including radius zero. Source: SU Theorem 1.6, p. 5,
local right-inverse derivation. -/
theorem continuous_deriv_polar_radius {f : ℂ → V}
    (hf : ContDiff ℝ 1 f) (z : ℂ) :
    Continuous (fun p : ℝ × ℝ =>
      deriv (fun r : ℝ => f (z - circleMap 0 r p.2)) p.1) := by
  simp_rw [(hasDerivAt_polar_radius (hf.differentiable (by simp)) z _ _).deriv]
  have h := continuous_polar_differential hf z
  apply Continuous.neg
  apply Continuous.clm_apply h
  simp only [circleMap_zero]
  fun_prop

/-- The angular derivative varies continuously over the full polar
rectangle. Source: SU Theorem 1.6, p. 5, local right-inverse derivation. -/
theorem continuous_deriv_polar_angle {f : ℂ → V}
    (hf : ContDiff ℝ 1 f) (z : ℂ) :
    Continuous (fun p : ℝ × ℝ =>
      deriv (fun θ : ℝ => f (z - circleMap 0 p.1 θ)) p.2) := by
  simp_rw [(hasDerivAt_polar_angle (hf.differentiable (by simp)) z _ _).deriv]
  apply Continuous.smul (continuous_fst.neg)
  apply Continuous.clm_apply (continuous_polar_differential hf z)
  simp only [circleMap_zero]
  fun_prop

variable [CompleteSpace V]

/-- The integral of an angular derivative vanishes by actual endpoint
periodicity. Source: SU Theorem 1.6, p. 5, local right-inverse derivation. -/
theorem integral_deriv_polar_angle {f : ℂ → V}
    (hf : ContDiff ℝ 1 f) (z : ℂ) (r : ℝ) :
    (∫ θ in (-Real.pi)..Real.pi,
      deriv (fun t : ℝ => f (z - circleMap 0 r t)) θ) = 0 := by
  have hc := (continuous_deriv_polar_angle hf z).comp
    ((continuous_const (y := r)).prodMk continuous_id)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ => (hasDerivAt_polar_angle
      (hf.differentiable (by simp)) z r θ).differentiableAt.hasDerivAt)
    (hc.intervalIntegrable _ _)]
  have he : circleMap 0 r (-Real.pi) = circleMap 0 r Real.pi := by
    have h := (periodic_circleMap 0 r) (-Real.pi)
    convert h.symm using 1
    congr 1
    ring
  rw [he, sub_self]

/-- The radial derivative integrates to the difference of the actual
endpoint values. Source: SU Theorem 1.6, p. 5, local right-inverse derivation. -/
theorem integral_deriv_polar_radius {f : ℂ → V}
    (hf : ContDiff ℝ 1 f) (z : ℂ) (θ : ℝ) :
    (∫ r in (0 : ℝ)..3,
      deriv (fun s : ℝ => f (z - circleMap 0 s θ)) r) =
      f (z - circleMap 0 3 θ) - f z := by
  have hc := (continuous_deriv_polar_radius hf z).comp
    (continuous_id.prodMk (continuous_const (y := θ)))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => (hasDerivAt_polar_radius
      (hf.differentiable (by simp)) z r θ).differentiableAt.hasDerivAt)
    (hc.intervalIntegrable _ _)]
  simp only [circleMap_zero_radius, Function.const_apply, sub_zero]

end PoincareMT.M60
