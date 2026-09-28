import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Acceleration


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

namespace PoincareConjecture.CoordinateExponential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem abs_linear_christoffel_le_of_scaled_controls
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {x v : E}
    (ell : E →L[ℝ] ℝ) {a d r ε : ℝ}
    (ha : 0 < a) (hd : 0 ≤ d) (hr : 0 < r) (hε : 0 ≤ ε)
    (hell : ∀ w, (a * r ^ 2) * ‖w‖ ^ 2 ≤ B x w w)
    (hjet : ‖fderiv ℝ B x‖ ≤ d * r ^ 2 * ε)
    (hunit : B x v v = 1) :
    |ell (christoffelBilinear B x v v)| ≤
      (3 * ‖ell‖ * d / (2 * a ^ 2)) * ε / r ^ 2 := by
  have har : 0 < a * r ^ 2 := mul_pos ha (sq_pos_of_pos hr)
  have hΓ := norm_coordinateChristoffel_le_of_ellipticity har hell hjet
  have hv : ‖v‖ ^ 2 ≤ 1 / (a * r ^ 2) := by
    apply (le_div_iff₀ har).mpr
    simpa only [hunit, mul_comm] using hell v
  calc
    |ell (christoffelBilinear B x v v)| ≤
        ‖ell‖ * ‖christoffelBilinear B x v v‖ := ell.le_opNorm _
    _ ≤ ‖ell‖ * (‖christoffelBilinear B x‖ * ‖v‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left ((christoffelBilinear B x).le_opNorm₂ _ _) (norm_nonneg _)
    _ = ‖ell‖ * ‖christoffelBilinear B x‖ * ‖v‖ ^ 2 := by ring
    _ ≤ ‖ell‖ * ((3 / (2 * (a * r ^ 2))) * (d * r ^ 2 * ε)) *
        (1 / (a * r ^ 2)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hΓ (norm_nonneg _)
      · exact hv
      · exact sq_nonneg _
      · positivity
    _ = (3 * ‖ell‖ * d / (2 * a ^ 2)) * ε / r ^ 2 := by
      field_simp

end PoincareConjecture.CoordinateExponential
