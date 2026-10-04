import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.InitialMetric.ConnectionDerivatives

/-!
# Reduction of the radial curvature coefficients

Morgan-Tian Lemma 12.2, printed pp. 294-295. The three coefficients of the
computed connection curvature reduce to rational expressions in the
profile, its slope and its second derivative. These scalar identities
are applied to the actual curvature in the next file. See the independent
F/G/H calculation in the M34 radial-curvature derivation and review.
-/

set_option autoImplicit false

namespace PoincareMT.M34

/-- Angular coefficient in the actual coordinate curvature formula
(Lemma 12.2, pp. 294-295). -/
theorem capCurvature_coefficient_F (a : ℝ) {r : ℝ} (hr : r ≠ 0)
    (hf : capProfile a r ≠ 0) :
    capChristoffelB a r - capChristoffelA a r +
        capChristoffelA a r * capChristoffelB a r * r ^ 2 =
      (1 - capSlope a r ^ 2) / r ^ 2 := by
  rw [capChristoffelA_eq a hr hf, capChristoffelB_eq a hr]
  field_simp
  ring

/-- Mixed radial coefficient in the coordinate curvature formula
(Lemma 12.2, pp. 294-295). -/
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

/-- Radial-output coefficient in the coordinate curvature formula
(Lemma 12.2, pp. 294-295). -/
theorem capCurvature_coefficient_H (a : ℝ) {r : ℝ} (hr : r ≠ 0)
    (hf : capProfile a r ≠ 0) :
    deriv (capChristoffelB a) r / r - capChristoffelC a r + capChristoffelB a r ^ 2 +
        capChristoffelB a r * capChristoffelC a r * r ^ 2 =
      (capSlope a r ^ 2 - 1 - capProfile a r * deriv (capSlope a) r) / r ^ 4 := by
  rw [capChristoffelC_eq a hr hf, (capChristoffelB_hasDerivAt a hr).deriv,
    capChristoffelA_eq a hr hf, capChristoffelB_eq a hr]
  field_simp
  ring

end PoincareMT.M34
