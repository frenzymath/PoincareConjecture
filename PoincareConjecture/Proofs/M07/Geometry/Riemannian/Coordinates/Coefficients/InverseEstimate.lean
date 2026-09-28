import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients.ChristoffelEstimate










set_option autoImplicit false
set_option maxSynthPendingDepth 8

namespace PoincareConjecture.CoordinateExponential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]


lemma norm_inverse_le_of_ellipticity {B : E →L[ℝ] E →L[ℝ] ℝ}
    {a : ℝ} (ha : 0 < a) (hell : ∀ v, a * ‖v‖ ^ 2 ≤ B v v) :
    ‖B.inverse‖ ≤ 1 / a := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro ξ
  simpa only [one_div_mul_eq_div] using norm_inverse_apply_le_of_ellipticity ha hell ξ

omit [FiniteDimensional ℝ E] in

lemma inverse_sub_inverse_apply {B C : E →L[ℝ] E →L[ℝ] ℝ}
    (hB : B.IsInvertible) (hC : C.IsInvertible) (ξ : E →L[ℝ] ℝ) :
    B.inverse ξ - C.inverse ξ = B.inverse ((C - B) (C.inverse ξ)) := by
  rw [sub_apply, hC.self_apply_inverse, map_sub,
    hB.inverse_apply_self]



lemma norm_inverse_sub_le_of_ellipticity {B C : E →L[ℝ] E →L[ℝ] ℝ}
    {a : ℝ} (ha : 0 < a)
    (hB : ∀ v, a * ‖v‖ ^ 2 ≤ B v v)
    (hC : ∀ v, a * ‖v‖ ^ 2 ≤ C v v) :
    ‖B.inverse - C.inverse‖ ≤ ‖B - C‖ / a ^ 2 := by
  have hiB := CoordinateTransition.isInvertible_of_uniformEllipticity ha hB
  have hiC := CoordinateTransition.isInvertible_of_uniformEllipticity ha hC
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro ξ
  rw [sub_apply, inverse_sub_inverse_apply hiB hiC]
  calc
    _ ≤ ‖(C - B) (C.inverse ξ)‖ / a := norm_inverse_apply_le_of_ellipticity ha hB _
    _ ≤ (‖C - B‖ * ‖C.inverse ξ‖) / a :=
      div_le_div_of_nonneg_right ((C - B).le_opNorm _) ha.le
    _ ≤ (‖C - B‖ * (‖ξ‖ / a)) / a :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (norm_inverse_apply_le_of_ellipticity ha hC ξ)
          (norm_nonneg _)) ha.le
    _ = (‖B - C‖ / a ^ 2) * ‖ξ‖ := by rw [norm_sub_rev]; ring



lemma norm_inverse_sub_le_of_modulus {B C : E →L[ℝ] E →L[ℝ] ℝ}
    {a H r : ℝ} (ha : 0 < a)
    (hB : ∀ v, a * ‖v‖ ^ 2 ≤ B v v)
    (hC : ∀ v, a * ‖v‖ ^ 2 ≤ C v v)
    (hmod : ‖B - C‖ ≤ H * r) :
    ‖B.inverse - C.inverse‖ ≤ (H / a ^ 2) * r := by
  calc
    _ ≤ ‖B - C‖ / a ^ 2 := norm_inverse_sub_le_of_ellipticity ha hB hC
    _ ≤ (H * r) / a ^ 2 := div_le_div_of_nonneg_right hmod (sq_nonneg _)
    _ = _ := by ring


lemma inner_inverse_innerSL_le {B : E →L[ℝ] E →L[ℝ] ℝ}
    {a : ℝ} (ha : 0 < a) (hell : ∀ v, a * ‖v‖ ^ 2 ≤ B v v) (v : E) :
    inner ℝ v (B.inverse (innerSL ℝ v)) ≤ ‖v‖ ^ 2 / a := by
  have h := norm_inverse_apply_le_of_ellipticity ha hell (innerSL ℝ v)
  rw [innerSL_apply_norm] at h
  calc
    _ ≤ |inner ℝ v (B.inverse (innerSL ℝ v))| := le_abs_self _
    _ ≤ ‖v‖ * ‖B.inverse (innerSL ℝ v)‖ := by
      simpa only [Real.norm_eq_abs, innerSL_apply_norm, innerSL_apply_apply] using
        (innerSL ℝ v).le_opNorm (B.inverse (innerSL ℝ v))
    _ ≤ ‖v‖ * (‖v‖ / a) := mul_le_mul_of_nonneg_left h (norm_nonneg v)
    _ = _ := by ring



lemma le_inner_inverse_innerSL {B : E →L[ℝ] E →L[ℝ] ℝ}
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hsymm : ∀ v w, B v w = B w v)
    (hlower : ∀ v, a * ‖v‖ ^ 2 ≤ B v v)
    (hupper : ∀ v, B v v ≤ b * ‖v‖ ^ 2) (v : E) :
    ‖v‖ ^ 2 / b ≤ inner ℝ v (B.inverse (innerSL ℝ v)) := by
  have hinv := CoordinateTransition.isInvertible_of_uniformEllipticity ha hlower
  let y := B.inverse (innerSL ℝ v)
  have hdual (w : E) : B y w = inner ℝ v w := by
    dsimp only [y]
    rw [hinv.self_apply_inverse]
    rfl
  have hvy : B v y = ‖v‖ ^ 2 := by
    rw [hsymm, hdual, real_inner_self_eq_norm_sq]
  have hyv : B y v = ‖v‖ ^ 2 := by rw [hdual, real_inner_self_eq_norm_sq]
  have hpos : 0 ≤ B (b • y - v) (b • y - v) :=
    (mul_nonneg ha.le (sq_nonneg _)).trans (hlower _)
  simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul,
    hvy, hyv, hdual] at hpos
  have hu := hupper v
  apply (div_le_iff₀ hb).mpr
  change ‖v‖ ^ 2 ≤ inner ℝ v y * b
  nlinarith

end PoincareConjecture.CoordinateExponential
