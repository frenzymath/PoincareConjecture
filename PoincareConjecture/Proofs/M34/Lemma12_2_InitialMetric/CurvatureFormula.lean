import PoincareConjecture.Proofs.M34.Lemma12_2_InitialMetric.CurvatureCoefficients
import PoincareConjecture.Proofs.M34.Mathlib.RadialConnectionDerivative
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Euclidean

set_option autoImplicit false

open Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M34

set_option backward.isDefEq.respectTransparency false in

theorem capCurvature_formula {a : ℝ} (ha : 0 < a) (hapi : a ≤ Real.pi / 2)
    (D : LeviCivitaData (capRiemannianMetric a ha hapi))
    {x : StandardCapSpace} (hx : x ≠ 0) (u v w : StandardCapSpace) :
    D.curvature x u v w =
      ((1 - capSlope a ‖x‖ ^ 2) / ‖x‖ ^ 2) •
        (inner ℝ v w • u - inner ℝ u w • v) +
      ((-deriv (capSlope a) ‖x‖ / (capProfile a ‖x‖ * ‖x‖ ^ 2) -
          (1 - capSlope a ‖x‖ ^ 2) / ‖x‖ ^ 4) * inner ℝ x w) •
        (inner ℝ x v • u - inner ℝ x u • v) +
      ((capSlope a ‖x‖ ^ 2 - 1 - capProfile a ‖x‖ * deriv (capSlope a) ‖x‖) / ‖x‖ ^ 4 *
        (inner ℝ x u * inner ℝ v w - inner ℝ x v * inner ℝ u w)) • x := by
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hf : capProfile a ‖x‖ ≠ 0 :=
    (capProfile_pos ha.le hapi (norm_pos_iff.mpr hx)).ne'
  have he (p q : StandardCapSpace) : D.euclideanConnection p q =ᶠ[𝓝 x]
      (fun y => Poincare.radialChristoffel (capChristoffelA a ‖y‖)
        (capChristoffelB a ‖y‖) (capChristoffelC a ‖y‖) y p q) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact capConnection_formula ha hapi D hy p q
  have hp (p q : StandardCapSpace) : D.euclideanConnection p q x =
      Poincare.radialChristoffel (capChristoffelA a ‖x‖)
        (capChristoffelB a ‖x‖) (capChristoffelC a ‖x‖) x p q :=
    capConnection_formula ha hapi D hx p q
  rw [D.curvature_eq_euclideanConnection, (he v w).fderiv_eq, (he u w).fderiv_eq]
  simp only [hp]
  have h := Poincare.radialChristoffel_curvature_expression hx
    (capChristoffelA_hasDerivAt a hr hf).differentiableAt.hasDerivAt
    (capChristoffelB_hasDerivAt a hr).differentiableAt.hasDerivAt
    (capChristoffelC_differentiableAt a hr hf).hasDerivAt u v w
  dsimp only at h
  rw [capCurvature_coefficient_F a hr hf, capCurvature_coefficient_G a hr hf,
    capCurvature_coefficient_H a hr hf] at h
  exact h

end PoincareConjecture.M34
