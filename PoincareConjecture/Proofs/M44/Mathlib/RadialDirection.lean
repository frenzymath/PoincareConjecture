import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv










set_option autoImplicit false

open Set
open scoped RealInnerProductSpace



theorem HasDerivAt.normalized_direction_of_radial
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {γ : ℝ → E} {t a : ℝ} (hγ : HasDerivAt γ (a • γ t) t) (hne : γ t ≠ 0) :
    HasDerivAt (fun s => ‖γ s‖⁻¹ • γ s) 0 t := by
  have hnorm : ‖γ t‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  have hn := hγ.norm_sq.sqrt (pow_ne_zero 2 hnorm)
  simp only [Real.sqrt_sq (norm_nonneg _), real_inner_smul_right,
    real_inner_self_eq_norm_sq] at hn
  have hn' : HasDerivAt (fun s => ‖γ s‖) (a * ‖γ t‖) t := by
    convert hn using 1
    field_simp
  have h := (hn'.inv hnorm).smul hγ
  convert h using 1
  · rfl
  · change 0 = ‖γ t‖⁻¹ • (a • γ t) + (-(a * ‖γ t‖) / ‖γ t‖ ^ 2) • γ t
    rw [smul_smul, ← add_smul]
    have hc : ‖γ t‖⁻¹ * a + -(a * ‖γ t‖) / ‖γ t‖ ^ 2 = 0 := by
      field_simp
      ring
    rw [hc, zero_smul]



theorem normalized_direction_eq_of_radial
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {γ : ℝ → E} {a : ℝ → ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hconn : IsPreconnected I)
    (hγ : ∀ t ∈ I, HasDerivAt γ (a t • γ t) t)
    (hne : ∀ t ∈ I, γ t ≠ 0) {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    ‖γ s‖⁻¹ • γ s = ‖γ t‖⁻¹ • γ t :=
  hI.is_const_of_deriv_eq_zero hconn
    (fun r hr =>
      ((hγ r hr).normalized_direction_of_radial (hne r hr)).differentiableAt.differentiableWithinAt)
    (fun r hr => ((hγ r hr).normalized_direction_of_radial (hne r hr)).deriv) hs ht
