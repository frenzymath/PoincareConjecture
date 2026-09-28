import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicTip
import PoincareConjecture.Proofs.M35.RadialGauge.FullForcingDerivative
import PoincareConjecture.Proofs.M35.RadialGauge.EvenQuadraticRemainder

set_option autoImplicit false

open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

open SmoothRadial

noncomputable def smoothTargetCoupling (f₀ : ℝ → ℝ) : ℝ → ℝ :=
  axisDivision (fun r => f₀ r * deriv f₀ r)

theorem smoothTargetCoupling_contDiff {f₀ : ℝ → ℝ} (hf : ContDiff ℝ ∞ f₀) :
    ContDiff ℝ ∞ (smoothTargetCoupling f₀) :=
  axisDivision_contDiff (hf.mul (contDiff_infty_iff_deriv.mp hf).2)

theorem smoothTargetCoupling_even {f₀ : ℝ → ℝ} (hf : ContDiff ℝ ∞ f₀)
    (ho : Function.Odd f₀) : Function.Even (smoothTargetCoupling f₀) := by
  have hdf := deriv_even_of_odd (hf.differentiable (by simp)) ho
  apply axisDivision_even_of_odd (hf.mul (contDiff_infty_iff_deriv.mp hf).2)
  intro r
  change f₀ (-r) * deriv f₀ (-r) = -(f₀ r * deriv f₀ r)
  rw [ho, hdf, neg_mul]

theorem smoothTargetCoupling_zero {f₀ : ℝ → ℝ} (hf : ContDiff ℝ ∞ f₀)
    (hf0 : f₀ 0 = 0) (hdf0 : deriv f₀ 0 = 1) :
    smoothTargetCoupling f₀ 0 = 1 := by
  rw [smoothTargetCoupling, axisDivision_zero]
  have hdf := (contDiff_infty_iff_deriv.mp hf).2
  change deriv (f₀ * deriv f₀) 0 = 1
  rw [(((hf.differentiable (by simp) 0).hasDerivAt).mul
    ((hdf.differentiable (by simp) 0).hasDerivAt)).deriv]
  simp only [hf0, hdf0, one_mul, zero_mul, add_zero]

theorem smoothTargetCoupling_eq_exterior {f₀ : ℝ → ℝ} (hf : ContDiff ℝ ∞ f₀)
    (hf0 : f₀ 0 = 0) {r : ℝ} (hr : r ≠ 0) :
    smoothTargetCoupling f₀ r = radialTargetCoupling f₀ r := by
  have h := mul_axisDivision (hf.mul (contDiff_infty_iff_deriv.mp hf).2) r
  simp only [hf0, zero_mul, sub_zero] at h
  change r * smoothTargetCoupling f₀ r = f₀ r * deriv f₀ r at h
  exact (eq_div_iff hr).mpr (by simpa only [mul_comm] using h)

theorem smoothTargetCoupling_contDiff_norm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f₀ : ℝ → ℝ} (hf : ContDiff ℝ ∞ f₀) (ho : Function.Odd f₀) :
    ContDiff ℝ ∞ (fun x : E => smoothTargetCoupling f₀ ‖x‖) :=
  contDiff_even_norm (smoothTargetCoupling_contDiff hf) (smoothTargetCoupling_even hf ho)

noncomputable def targetQuadraticRemainder (f₀ : ℝ → ℝ) : ℝ → ℝ :=
  smoothEvenQuadratic (smoothTargetCoupling f₀)

theorem targetQuadraticRemainder_contDiff {f₀ : ℝ → ℝ} (hf : ContDiff ℝ ∞ f₀) :
    ContDiff ℝ ∞ (targetQuadraticRemainder f₀) :=
  smoothEvenQuadratic_contDiff (smoothTargetCoupling_contDiff hf)

theorem targetQuadraticRemainder_even {f₀ : ℝ → ℝ} (hf : ContDiff ℝ ∞ f₀)
    (ho : Function.Odd f₀) : Function.Even (targetQuadraticRemainder f₀) :=
  smoothEvenQuadratic_even (smoothTargetCoupling_contDiff hf) (smoothTargetCoupling_even hf ho)

theorem targetQuadraticRemainder_identity {f₀ : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f₀) (ho : Function.Odd f₀)
    (hf0 : f₀ 0 = 0) (hdf0 : deriv f₀ 0 = 1) (r : ℝ) :
    r ^ 2 * targetQuadraticRemainder f₀ r = smoothTargetCoupling f₀ r - 1 := by
  rw [targetQuadraticRemainder, smoothEvenQuadratic_identity
    (smoothTargetCoupling_contDiff hf) (smoothTargetCoupling_even hf ho),
    smoothTargetCoupling_zero hf hf0 hdf0]

end PoincareConjecture.M35.RadialGauge
