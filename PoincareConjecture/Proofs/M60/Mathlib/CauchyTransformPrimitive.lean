import PoincareConjecture.Proofs.M60.Mathlib.PolarRestrictionIntegral

set_option autoImplicit false

open Complex Set MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture.M60

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]

omit [IsScalarTower ℝ ℂ V] in

theorem continuous_cauchyRiemannDerivative {f : ℂ → V} (hf : ContDiff ℝ 1 f) :
    Continuous (cauchyRiemannDerivative f) := by
  have hd := hf.continuous_fderiv (by simp)
  exact ((hd.clm_apply continuous_const).add
    ((hd.clm_apply continuous_const).const_smul I)).const_smul (1 / 2 : ℝ)

variable [CompleteSpace V]

private theorem integral_cauchyRiemannDerivative_angle {f : ℂ → V}
    (hf : ContDiff ℝ 1 f) (z : ℂ) {r : ℝ} (hr : r ≠ 0) :
    (∫ θ in (-Real.pi)..Real.pi,
      (circleMap 0 1 θ)⁻¹ • cauchyRiemannDerivative f (z - circleMap 0 r θ)) =
      -(1 / 2 : ℝ) • (∫ θ in (-Real.pi)..Real.pi,
        deriv (fun s : ℝ => f (z - circleMap 0 s θ)) r) := by
  have hrad := ((continuous_deriv_polar_radius hf z).comp
    ((continuous_const (y := r)).prodMk continuous_id)).intervalIntegrable
      (μ := volume) (-Real.pi) Real.pi
  have hang := ((continuous_deriv_polar_angle hf z).comp
    ((continuous_const (y := r)).prodMk continuous_id)).intervalIntegrable
      (μ := volume) (-Real.pi) Real.pi
  dsimp only [Function.comp_def, id_eq] at hrad hang
  have h1 : IntervalIntegrable (fun θ => -(1 / 2 : ℝ) •
      deriv (fun s : ℝ => f (z - circleMap 0 s θ)) r) volume (-Real.pi) Real.pi :=
    hrad.smul _
  have h2 : IntervalIntegrable (fun θ => (1 / (2 * r) : ℝ) • I •
      deriv (fun t : ℝ => f (z - circleMap 0 r t)) θ) volume (-Real.pi) Real.pi :=
    (hang.smul I).smul _
  simp_rw [cauchyRiemannDerivative_polar (hf.differentiable (by simp)) z hr]
  rw [intervalIntegral.integral_sub h1 h2]
  simp only [intervalIntegral.integral_smul, integral_deriv_polar_angle hf,
    smul_zero, sub_zero]

theorem cauchyTransform_cauchyRiemannDerivative {f : ℂ → V}
    (hf : ContDiff ℝ 1 f) (z : ℂ) :
    cauchyTransform (cauchyRiemannDerivative f) z =
      -(1 / (2 * Real.pi) : ℝ) •
        (∫ θ in (-Real.pi)..Real.pi, f (z - circleMap 0 3 θ) - f z) := by
  rw [cauchyTransform_eq_iterated_polar (continuous_cauchyRiemannDerivative hf)]
  simp_rw [intervalIntegral.integral_smul]
  have he : (∫ r in (0 : ℝ)..3, ∫ θ in (-Real.pi)..Real.pi,
      (circleMap 0 1 θ)⁻¹ • cauchyRiemannDerivative f (z - circleMap 0 r θ)) =
      ∫ r in (0 : ℝ)..3, -(1 / 2 : ℝ) •
        (∫ θ in (-Real.pi)..Real.pi,
          deriv (fun s : ℝ => f (z - circleMap 0 s θ)) r) := by
    rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 3 by norm_num),
      intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 3 by norm_num)]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    exact integral_cauchyRiemannDerivative_angle hf z hr.1.ne'
  rw [he, intervalIntegral.integral_smul]
  have hint : IntegrableOn
      (fun p : ℝ × ℝ => deriv (fun s : ℝ => f (z - circleMap 0 s p.2)) p.1)
      (uIoc (0 : ℝ) 3 ×ˢ uIoc (-Real.pi) Real.pi) := by
    apply ((continuous_deriv_polar_radius hf z).continuousOn.integrableOn_compact
      (isCompact_uIcc.prod isCompact_uIcc)).mono_set
    exact Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc
  rw [intervalIntegral_intervalIntegral_swap
    (F := fun r θ : ℝ => deriv (fun s : ℝ => f (z - circleMap 0 s θ)) r) hint]
  simp_rw [integral_deriv_polar_radius hf z]
  rw [smul_smul]
  congr 1
  ring

end PoincareConjecture.M60
