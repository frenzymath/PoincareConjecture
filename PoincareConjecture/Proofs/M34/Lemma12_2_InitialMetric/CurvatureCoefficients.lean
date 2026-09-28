import PoincareConjecture.Proofs.M34.Lemma12_2_InitialMetric.ConnectionDerivatives

set_option autoImplicit false

namespace PoincareConjecture.M34

theorem capCurvature_coefficient_F (a : ℝ) {r : ℝ} (hr : r ≠ 0)
    (hf : capProfile a r ≠ 0) :
    capChristoffelB a r - capChristoffelA a r +
        capChristoffelA a r * capChristoffelB a r * r ^ 2 =
      (1 - capSlope a r ^ 2) / r ^ 2 := by
  rw [capChristoffelA_eq a hr hf, capChristoffelB_eq a hr]
  field_simp
  ring

theorem capCurvature_coefficient_G (a : ℝ) {r : ℝ} (hr : r ≠ 0)
    (hf : capProfile a r ≠ 0) :
    capChristoffelC a r - deriv (capChristoffelA a) r / r + capChristoffelA a r ^ 2 +
        capChristoffelA a r * capChristoffelC a r * r ^ 2 =
      -deriv (capSlope a) r / (capProfile a r * r ^ 2) -
        (1 - capSlope a r ^ 2) / r ^ 4 := by
  rw [capChristoffelC_eq a hr hf, (capChristoffelA_hasDerivAt a hr hf).deriv,
    capChristoffelA_eq a hr hf, capChristoffelB_eq a hr]
  field_simp
  ring

theorem capCurvature_coefficient_H (a : ℝ) {r : ℝ} (hr : r ≠ 0)
    (hf : capProfile a r ≠ 0) :
    deriv (capChristoffelB a) r / r - capChristoffelC a r + capChristoffelB a r ^ 2 +
        capChristoffelB a r * capChristoffelC a r * r ^ 2 =
      (capSlope a r ^ 2 - 1 - capProfile a r * deriv (capSlope a) r) / r ^ 4 := by
  rw [capChristoffelC_eq a hr hf, (capChristoffelB_hasDerivAt a hr).deriv,
    capChristoffelA_eq a hr hf, capChristoffelB_eq a hr]
  field_simp
  ring

end PoincareConjecture.M34
