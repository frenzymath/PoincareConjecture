import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients.InverseBounds
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Jacobi.Coefficients










set_option autoImplicit false

set_option maxSynthPendingDepth 8

namespace PoincareConjecture.CoordinateExponential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]


lemma norm_inverse_apply_le_of_ellipticity {B : E →L[ℝ] E →L[ℝ] ℝ}
    {a : ℝ} (ha : 0 < a) (hell : ∀ v, a * ‖v‖ ^ 2 ≤ B v v)
    (ξ : E →L[ℝ] ℝ) : ‖B.inverse ξ‖ ≤ ‖ξ‖ / a := by
  have hinv := CoordinateTransition.isInvertible_of_uniformEllipticity ha hell
  have h := hell (B.inverse ξ)
  rw [hinv.self_apply_inverse] at h
  have hbound := h.trans ((le_abs_self _).trans (ξ.le_opNorm (B.inverse ξ)))
  apply (le_div_iff₀ ha).mpr
  by_cases hz : ‖B.inverse ξ‖ = 0
  · simp [hz]
  · have hp : 0 < ‖B.inverse ξ‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith

omit [FiniteDimensional ℝ E] in


lemma norm_metricKoszulCovector_le (B : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (v w : E) : ‖metricKoszulCovector B v w‖ ≤ (3 / 2 : ℝ) * ‖B‖ * ‖v‖ * ‖w‖ := by
  have h₁ := B.le_opNorm₂ v w
  have h₂ : ‖(B w).flip v‖ ≤ ‖B‖ * ‖v‖ * ‖w‖ := by
    calc
      _ ≤ ‖(B w).flip‖ * ‖v‖ := (B w).flip.le_opNorm v
      _ = ‖B w‖ * ‖v‖ := by rw [ContinuousLinearMap.opNorm_flip]
      _ ≤ (‖B‖ * ‖w‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (B.le_opNorm w) (norm_nonneg v)
      _ = _ := by ring
  have h₃ : ‖(B.flip v).flip w‖ ≤ ‖B‖ * ‖v‖ * ‖w‖ := by
    calc
      _ ≤ ‖(B.flip v).flip‖ * ‖w‖ := (B.flip v).flip.le_opNorm w
      _ = ‖B.flip v‖ * ‖w‖ := by rw [ContinuousLinearMap.opNorm_flip]
      _ ≤ (‖B.flip‖ * ‖v‖) * ‖w‖ :=
        mul_le_mul_of_nonneg_right (B.flip.le_opNorm v) (norm_nonneg w)
      _ = _ := by rw [ContinuousLinearMap.opNorm_flip]
  have hsum := (norm_sub_le (B v w + (B w).flip v) ((B.flip v).flip w)).trans
    (add_le_add (norm_add_le _ _) le_rfl)
  rw [metricKoszulCovector, norm_smul]
  norm_num only [Real.norm_eq_abs, abs_inv, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith



lemma norm_christoffelBilinear_le_of_ellipticity
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E) {a : ℝ}
    (ha : 0 < a) (hell : ∀ v, a * ‖v‖ ^ 2 ≤ B x v v) :
    ‖christoffelBilinear B x‖ ≤ (3 / (2 * a)) * ‖fderiv ℝ B x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro v w
  change ‖(B x).inverse (metricKoszulCovector (fderiv ℝ B x) v w)‖ ≤ _
  calc
    _ ≤ ‖metricKoszulCovector (fderiv ℝ B x) v w‖ / a :=
      norm_inverse_apply_le_of_ellipticity ha hell _
    _ ≤ ((3 / 2 : ℝ) * ‖fderiv ℝ B x‖ * ‖v‖ * ‖w‖) / a :=
      div_le_div_of_nonneg_right (norm_metricKoszulCovector_le _ v w) ha.le
    _ = _ := by ring

end PoincareConjecture.CoordinateExponential
