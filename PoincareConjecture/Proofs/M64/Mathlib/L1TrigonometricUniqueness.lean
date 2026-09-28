import PoincareConjecture.Proofs.M64.Mathlib.L1FourierUniqueness












set_option autoImplicit false
set_option warningAsError true

noncomputable section

open Set Filter MeasureTheory

namespace PoincareConjecture





theorem m64L1Trigonometric_eq_zero {f : ℝ → ℝ}
    (hf : IntegrableOn f (Icc 0 (2 * Real.pi)))
    (hc : ∀ j : ℤ, (∫ x in Icc 0 (2 * Real.pi), Real.cos (j * x) * f x) = 0)
    (hs : ∀ j : ℤ, (∫ x in Icc 0 (2 * Real.pi), Real.sin (j * x) * f x) = 0) :
    f =ᵐ[volume.restrict (Icc 0 (2 * Real.pi))] (fun _ => 0) := by
  have hi : IntegrableOn (fun x => (f x : ℂ)) (Icc 0 (2 * Real.pi)) :=
    Complex.ofRealCLM.integrable_comp hf
  have hchar (j : ℤ) (x : ℝ) :
      fourier j (x : AddCircle (2 * Real.pi)) =
        (Real.cos (j * x) : ℂ) + (Real.sin (j * x) : ℂ) * Complex.I := by
    rw [fourier_coe_apply]
    have he : (2 * (Real.pi : ℂ) * Complex.I * j * x / (2 * Real.pi)) =
        ((j * x : ℝ) : ℂ) * Complex.I := by
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
    rw [Complex.ofReal_mul, Complex.ofReal_ofNat, he, Complex.exp_ofReal_mul_I]
  have hzero := m64L1Fourier_eq_zero (by positivity : (0 : ℝ) < 2 * Real.pi) hi (by
    intro j
    have hci : IntegrableOn (fun x => Real.cos (j * x) * f x) (Icc 0 (2 * Real.pi)) :=
      hf.bdd_mul
        (Real.continuous_cos.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
        (Eventually.of_forall fun x => by
          simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (j * x))
    have hsi : IntegrableOn (fun x => Real.sin (j * x) * f x) (Icc 0 (2 * Real.pi)) :=
      hf.bdd_mul
        (Real.continuous_sin.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
        (Eventually.of_forall fun x => by
          simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (j * x))
    have hciC : IntegrableOn (fun x => ((Real.cos (j * x) * f x : ℝ) : ℂ))
        (Icc 0 (2 * Real.pi)) := Complex.ofRealCLM.integrable_comp hci
    have hsiC : IntegrableOn (fun x => ((Real.sin (j * x) * f x : ℝ) : ℂ))
        (Icc 0 (2 * Real.pi)) := Complex.ofRealCLM.integrable_comp hsi
    calc
      _ = ∫ x in Icc 0 (2 * Real.pi),
          ((Real.cos (j * x) * f x : ℝ) : ℂ) +
            ((Real.sin (j * x) * f x : ℝ) : ℂ) * Complex.I := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          change fourier j (x : AddCircle (2 * Real.pi)) * (f x : ℂ) = _
          rw [hchar]
          push_cast
          ring
      _ = 0 := by
        rw [integral_add hciC (hsiC.mul_const Complex.I),
          integral_mul_const, integral_complex_ofReal, integral_complex_ofReal, hc, hs]
        simp)
  filter_upwards [hzero] with x hx
  exact Complex.ofReal_eq_zero.mp hx

end PoincareConjecture
