import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.RadialIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus










set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace PoincareConjecture.M35.SmoothRadial


noncomputable def axisDivision (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  CoordinateExponential.radialWeightedIntegral 0 (deriv f) r

theorem axisDivision_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (axisDivision f) := by
  have hd : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  apply contDiff_iff_contDiffAt.mpr
  intro r
  have hr : r ∈ Metric.ball (0 : ℝ) (‖r‖ + 1) := by simp
  exact (CoordinateExponential.contDiffOn_radialWeightedIntegral 0
    (r := ‖r‖ + 1) hd.contDiffOn r hr).contDiffAt (Metric.isOpen_ball.mem_nhds hr)


theorem mul_axisDivision {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (r : ℝ) :
    r * axisDivision f r = f r - f 0 := by
  have hsub := intervalIntegral.integral_deriv_eq_sub
    (a := (0 : ℝ)) (b := r) (fun x _ => hf.differentiable (by simp) x)
    ((contDiff_infty_iff_deriv.mp hf).2.continuous.intervalIntegrable 0 r)
  have hscale := intervalIntegral.mul_integral_comp_mul_left
    (f := deriv f) r (a := (0 : ℝ)) (b := 1)
  simp only [mul_zero, mul_one] at hscale
  simpa only [axisDivision, CoordinateExponential.radialWeightedIntegral,
    pow_zero, smul_eq_mul, one_mul, mul_one, mul_comm] using hscale.trans hsub

theorem axisDivision_zero {f : ℝ → ℝ} : axisDivision f 0 = deriv f 0 := by
  simp [axisDivision, CoordinateExponential.radialWeightedIntegral]


theorem deriv_odd_of_even {f : ℝ → ℝ} (hf : Differentiable ℝ f) (he : Function.Even f) :
    Function.Odd (deriv f) := by
  intro r
  have hc := (hf (-r)).hasDerivAt.comp r (hasDerivAt_id r).neg
  have hd : HasDerivAt f (-deriv f (-r)) r := by
    convert! hc using 1
    · funext a
      exact (he a).symm
    · ring
  have h := hd.unique (hf r).hasDerivAt
  linarith only [h]


theorem deriv_even_of_odd {f : ℝ → ℝ} (hf : Differentiable ℝ f) (ho : Function.Odd f) :
    Function.Even (deriv f) := by
  intro r
  have hc := (hf (-r)).hasDerivAt.comp r (hasDerivAt_id r).neg
  have hd : HasDerivAt (fun a => -f a) (-deriv f (-r)) r := by
    convert! hc using 1
    · funext a
      exact (ho a).symm
    · ring
  have h := hd.unique (hf r).hasDerivAt.neg
  linarith only [h]

theorem deriv_zero_of_even {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (he : Function.Even f) : deriv f 0 = 0 := by
  have h := deriv_odd_of_even hf he 0
  rw [neg_zero] at h
  linarith only [h]


theorem axisDivision_even_of_odd {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (ho : Function.Odd f) : Function.Even (axisDivision f) := by
  intro r
  have hd := deriv_even_of_odd (hf.differentiable (by simp)) ho
  unfold axisDivision CoordinateExponential.radialWeightedIntegral
  apply intervalIntegral.integral_congr
  intro t _
  simp only [pow_zero, smul_eq_mul, one_mul, mul_neg]
  exact hd (t * r)



theorem axisDivision_deriv_even {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) : Function.Even (axisDivision (deriv f)) :=
  axisDivision_even_of_odd (contDiff_infty_iff_deriv.mp hf).2
    (deriv_odd_of_even (hf.differentiable (by simp)) he)

theorem mul_axisDivision_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (r : ℝ) : r * axisDivision (deriv f) r = deriv f r := by
  rw [mul_axisDivision (contDiff_infty_iff_deriv.mp hf).2,
    deriv_zero_of_even (hf.differentiable (by simp)) he, sub_zero]

end PoincareConjecture.M35.SmoothRadial
