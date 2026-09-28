import PoincareConjecture.Proofs.M34.Lemma12_2_InitialMetric.CoefficientCalculus

set_option autoImplicit false

open Filter
open scoped Topology ContDiff

namespace PoincareConjecture.M34

theorem capChristoffelA_hasDerivAt (a : ℝ) {r : ℝ} (hr : r ≠ 0)
    (hf : capProfile a r ≠ 0) :
    HasDerivAt (capChristoffelA a)
      (deriv (capSlope a) r / (r * capProfile a r) -
        capSlope a r / (r ^ 2 * capProfile a r) -
        capSlope a r ^ 2 / (r * capProfile a r ^ 2) + 2 / r ^ 3) r := by
  have he : capChristoffelA a =ᶠ[𝓝 r]
      (fun s => capSlope a s / (s * capProfile a s) - 1 / s ^ 2) := by
    filter_upwards [eventually_ne_nhds hr,
      (capProfile_contDiff a).continuous.continuousAt.eventually_ne hf] with s hs hfs
    exact capChristoffelA_eq a hs hfs
  have hp := ((capSlope_contDiff_right a).differentiable (by simp) r).hasDerivAt
  have h := (hp.div ((hasDerivAt_id r).mul (capProfile_hasDerivAt a r))
    (mul_ne_zero hr hf)).sub
    ((hasDerivAt_const r (1 : ℝ)).div ((hasDerivAt_id r).pow 2) (pow_ne_zero 2 hr))
  convert! h.congr_of_eventuallyEq he using 1
  simp only [Pi.mul_apply, Pi.pow_apply, id_eq]
  field_simp
  ring

theorem capChristoffelB_hasDerivAt (a : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (capChristoffelB a)
      (-(2 + capSlope a r ^ 2 + capProfile a r * deriv (capSlope a) r) / r ^ 3 +
        3 * capProfile a r * capSlope a r / r ^ 4) r := by
  have he : capChristoffelB a =ᶠ[𝓝 r]
      (fun s => 1 / s ^ 2 - capProfile a s * capSlope a s / s ^ 3) := by
    filter_upwards [eventually_ne_nhds hr] with s hs
    exact capChristoffelB_eq a hs
  have hp := ((capSlope_contDiff_right a).differentiable (by simp) r).hasDerivAt
  have h := ((hasDerivAt_const r (1 : ℝ)).div ((hasDerivAt_id r).pow 2)
    (pow_ne_zero 2 hr)).sub
    (((capProfile_hasDerivAt a r).mul hp).div ((hasDerivAt_id r).pow 3) (pow_ne_zero 3 hr))
  convert! h.congr_of_eventuallyEq he using 1
  simp only [Pi.mul_apply, Pi.pow_apply, id_eq]
  field_simp
  ring

theorem capChristoffelC_differentiableAt (a : ℝ) {r : ℝ} (hr : r ≠ 0)
    (hf : capProfile a r ≠ 0) : DifferentiableAt ℝ (capChristoffelC a) r := by
  have he : capChristoffelC a =ᶠ[𝓝 r]
      (fun s => -(2 * capChristoffelA a s + capChristoffelB a s) / s ^ 2) := by
    filter_upwards [eventually_ne_nhds hr,
      (capProfile_contDiff a).continuous.continuousAt.eventually_ne hf] with s hs hfs
    exact capChristoffelC_eq a hs hfs
  have h := ((((capChristoffelA_hasDerivAt a hr hf).const_mul 2).add
    (capChristoffelB_hasDerivAt a hr)).neg.div ((hasDerivAt_id r).pow 2)
    (pow_ne_zero 2 hr))
  exact (h.congr_of_eventuallyEq he).differentiableAt

end PoincareConjecture.M34
