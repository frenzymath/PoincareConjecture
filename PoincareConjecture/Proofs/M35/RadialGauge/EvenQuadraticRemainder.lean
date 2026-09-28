import PoincareConjecture.Proofs.M35.Mathlib.SmoothEvenRadial









set_option autoImplicit false

open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

open SmoothRadial

theorem axisDivision_odd_of_even {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (he : Function.Even F) : Function.Odd (axisDivision F) := by
  intro r
  by_cases hr : r = 0
  · subst r
    rw [neg_zero, axisDivision_zero, deriv_zero_of_even (hF.differentiable (by simp)) he]
    exact neg_zero.symm
  · have hp := mul_axisDivision hF r
    have hn := mul_axisDivision hF (-r)
    rw [he r] at hn
    have heq : (-r) * axisDivision F (-r) = (-r) * -axisDivision F r := by
      linarith only [hp, hn]
    exact mul_left_cancel₀ (neg_ne_zero.mpr hr) heq


noncomputable def smoothEvenQuadratic (F : ℝ → ℝ) : ℝ → ℝ := axisDivision (axisDivision F)

theorem smoothEvenQuadratic_contDiff {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (smoothEvenQuadratic F) :=
  axisDivision_contDiff (axisDivision_contDiff hF)

theorem smoothEvenQuadratic_even {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (he : Function.Even F) : Function.Even (smoothEvenQuadratic F) :=
  axisDivision_even_of_odd (axisDivision_contDiff hF) (axisDivision_odd_of_even hF he)

theorem smoothEvenQuadratic_identity {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (he : Function.Even F) (r : ℝ) : r ^ 2 * smoothEvenQuadratic F r = F r - F 0 := by
  have h1 := mul_axisDivision hF r
  have h2 := mul_axisDivision (axisDivision_contDiff hF) r
  rw [axisDivision_zero, deriv_zero_of_even (hF.differentiable (by simp)) he, sub_zero] at h2
  change r * smoothEvenQuadratic F r = axisDivision F r at h2
  calc
    _ = r * (r * smoothEvenQuadratic F r) := by ring
    _ = _ := by rw [h2, h1]

theorem smoothEvenQuadratic_contDiff_norm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (he : Function.Even F) :
    ContDiff ℝ ∞ (fun x : E => smoothEvenQuadratic F ‖x‖) :=
  contDiff_even_norm (smoothEvenQuadratic_contDiff hF) (smoothEvenQuadratic_even hF he)

end PoincareConjecture.M35.RadialGauge
