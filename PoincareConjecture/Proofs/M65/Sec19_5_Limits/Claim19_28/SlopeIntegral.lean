import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.SlopeDerivative
import PoincareConjecture.Definitions.M63Ramp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false

open Bundle Manifold Set
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

theorem m65CircleLift_velocity_pairing (C : M62.CircleGeometry circumference)
    (lift : ℝ → ℝ) (hlift : ContDiff ℝ 2 lift) (x : ℝ) :
    C.metricOnPoints.inner (C.quotient (lift x))
      (curveVelocity (C.quotient ∘ lift) x) (C.frame (C.quotient (lift x))) =
        deriv lift x := by
  let := C.chartedSpace
  have hd := (hlift.differentiable (by norm_num) x).mdifferentiableAt
  have hchain := mfderiv_comp_apply (f := lift) (g := C.quotient) x
    (C.quotient_smooth.mdifferentiableAt (by simp)) hd (1 : ℝ)
  change curveVelocity (C.quotient ∘ lift) x = _ at hchain
  have hvel : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) lift x (1 : ℝ) = deriv lift x := by
    simpa +instances only [mfderiv_eq_fderiv] using!
      (fderiv_apply_one_eq_deriv (f := lift) (x := x))
  erw [hvel] at hchain
  rw [hchain]
  change C.metricOnPoints.inner (lift x : C.Point)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) C.quotient (lift x) (deriv lift x))
    (C.frame (lift x : C.Point)) = deriv lift x
  rw [C.frame_quotient]
  simpa +instances only [mul_one] using!
    C.metric_quotient (lift x) (deriv lift x) 1

theorem m65Slope_mul_speed_eq_lift_deriv (P : M62.CircleProductData F circumference)
    (c : ℝ → ℝ → P.charts.Point) (hc : M62ShrinkingCurve P.flow c)
    {t : ℝ} (ht : t ∈ Icc a b) (L : M63PositiveDegreeLift P (fun x => c x t))
    (x : ℝ) :
    m62Slope P c t x * curveSpeed P.flow c t x = deriv L.lift x := by
  let := P.charts.chartedSpace
  have hsnd : ContMDiff (𝓡 (n + 1)) (𝓡 1) ∞
      (Prod.snd : P.charts.Point → P.circle.Point) :=
    contMDiff_snd.comp P.charts.to_product_smooth
  have hcurve := (hc.spatial_regular t ht x).mdifferentiableAt (by norm_num)
  have hchain := mfderiv_comp_apply (f := fun y => c y t)
    (g := (Prod.snd : P.charts.Point → P.circle.Point)) x
    (hsnd.mdifferentiableAt (by simp)) hcurve (1 : ℝ)
  change curveVelocity (fun y => (c y t).2) x = _ at hchain
  rw [← P.charts.split_circle] at hchain
  have hquotient : (fun y => (c y t).2) = P.circle.quotient ∘ L.lift :=
    funext (fun y => (L.quotient_eq y).symm)
  have hpair := m65CircleLift_velocity_pairing P.circle L.lift L.regular x
  rw [← hquotient] at hpair
  change P.circle.metricOnPoints.inner ((P.circle.quotient ∘ L.lift) x)
    (curveVelocity (fun y => (c y t).2) x)
      (P.circle.frame ((P.circle.quotient ∘ L.lift) x)) = _ at hpair
  rw [← hquotient, hchain] at hpair
  unfold m62Slope spatialUnitTangent
  rw [P.metric_eq]
  simp only [map_smul, M62.CircleProductCharts.circleUnit,
    ContinuousLinearEquiv.apply_symm_apply, Prod.smul_fst, Prod.smul_snd,
    map_zero, zero_add, smul_apply, smul_eq_mul]
  erw [hpair]
  have hv := (M62.speed_pos P.flow c hc ht x).ne'
  field_simp

theorem m65Slope_integral_period_eq_circumference
    (P : M62.CircleProductData F circumference)
    (c : ℝ → ℝ → P.charts.Point) (hc : M62ShrinkingCurve P.flow c)
    {t : ℝ} (ht : t ∈ Icc a b) (L : M63PositiveDegreeLift P (fun x => c x t))
    (hdegree : L.degree = 1) (start : ℝ) :
    (∫ x in start..start + curvePeriod,
      m62Slope P c t x * curveSpeed P.flow c t x) = circumference := by
  have heq := funext (m65Slope_mul_speed_eq_lift_deriv P c hc ht L)
  rw [heq]
  rw [intervalIntegral.integral_deriv_eq_sub
    (fun x _ => L.regular.differentiable (by norm_num) x)
    ((L.regular.continuous_deriv (by norm_num)).intervalIntegrable _ _)]
  have hp := L.period_shift start
  rw [hdegree, Nat.cast_one, one_mul] at hp
  linarith

theorem m65Slope_integral_eq_circumference (P : M62.CircleProductData F circumference)
    (c : ℝ → ℝ → P.charts.Point) (hc : M62ShrinkingCurve P.flow c)
    {t : ℝ} (ht : t ∈ Icc a b) (L : M63PositiveDegreeLift P (fun x => c x t))
    (hdegree : L.degree = 1) :
    (∫ x in (0 : ℝ)..curvePeriod,
      m62Slope P c t x * curveSpeed P.flow c t x) = circumference := by
  simpa only [zero_add] using
    m65Slope_integral_period_eq_circumference P c hc ht L hdegree 0

end PoincareConjecture
