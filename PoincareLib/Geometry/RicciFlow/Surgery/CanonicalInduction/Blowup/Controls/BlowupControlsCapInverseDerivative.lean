import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Blowup.Controls.BlowupControlsCapInverseMetric

/-!
# Differentiating the actual inverse metric

The inverse is differentiated as the actual inverse continuous linear
operator. Its derivative has both inverse factors, with their order
unchanged. Source: Morgan--Tian, Definition 9.72, pp. 230-231.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareMT.M47

section Operator

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The derivative of an actual inverse operator, with both inverse
factors kept in the correct noncommutative order. -/
theorem cap_inverse_fderiv_apply (A : V → E →L[ℝ] E) {x : V}
    (hA : DifferentiableAt ℝ A x) (hi : (A x).IsInvertible) (v : V) :
    fderiv ℝ (fun y => (A y).inverse) x v =
      -((A x).inverse * (fderiv ℝ A x v) * (A x).inverse) := by
  let a : (E →L[ℝ] E)ˣ :=
    { val := A x
      inv := (A x).inverse
      val_inv := by
        exact hi.self_comp_inverse
      inv_val := by
        exact hi.inverse_comp_self }
  have h := (hasFDerivAt_ringInverse (𝕜 := ℝ) a).comp x hA.hasFDerivAt
  have hd := congrArg (fun L : V →L[ℝ] E →L[ℝ] E => L v) h.fderiv
  rw [ContinuousLinearMap.ringInverse_eq_inverse] at hd
  exact hd

/-- The operator derivative estimate keeps the squared reciprocal
ellipticity factor supplied by the actual inverse norm. -/
theorem cap_inverse_fderiv_norm_le (A : V → E →L[ℝ] E) {x : V}
    (hA : DifferentiableAt ℝ A x) (hi : (A x).IsInvertible)
    {a : ℝ} (ha : 0 ≤ a) (hbound : ‖(A x).inverse‖ ≤ a) (v : V) :
    ‖fderiv ℝ (fun y => (A y).inverse) x v‖ ≤
      a ^ 2 * ‖fderiv ℝ A x v‖ := by
  rw [cap_inverse_fderiv_apply A hA hi v, norm_neg]
  calc
    _ ≤ (‖(A x).inverse‖ * ‖fderiv ℝ A x v‖) * ‖(A x).inverse‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (a * ‖fderiv ℝ A x v‖) * a :=
      mul_le_mul (mul_le_mul_of_nonneg_right hbound (norm_nonneg _))
        hbound (norm_nonneg _) (mul_nonneg ha (norm_nonneg _))
    _ = _ := by ring

end Operator

end PoincareMT.M47
