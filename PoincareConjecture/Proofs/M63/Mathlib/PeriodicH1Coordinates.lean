import PoincareConjecture.Proofs.M63.Mathlib.PeriodicSobolevJets

set_option autoImplicit false

open AddCircle MeasureTheory
open scoped ENNReal

namespace PoincareConjecture.M63

variable {L : ℝ} [Fact (0 < L)]

theorem fourierCoeff_circle_derivative (f f1 : C(AddCircle L, ℂ))
    (hf : ∀ x : ℝ, HasDerivAt (fun y : ℝ => f (y : AddCircle L)) (f1 (x : AddCircle L)) x)
    (n : ℤ) :
    fourierCoeff f1 n = Complex.I * ((2 * Real.pi * (n : ℝ) / L : ℝ) : ℂ) *
      fourierCoeff f n := by
  have hcoeff (g : C(AddCircle L, ℂ)) :
      fourierCoeffOn (Fact.out : 0 < L) (fun x : ℝ => g (x : AddCircle L)) n =
        fourierCoeff g n := by
    rw [fourierCoeffOn_eq_integral, fourierCoeff_eq_intervalIntegral g n 0]
    simp only [fourier_coe_apply, sub_zero, zero_add]
  have hb : f (L : AddCircle L) = f (0 : AddCircle L) := by
    rw [AddCircle.coe_period]
  have h := fourierCoeffOn_derivative (Fact.out : 0 < L) hf
    (f1.continuous.comp (AddCircle.continuous_mk' L)) hb n
  simpa only [hcoeff, sub_zero] using h

theorem hasSum_periodicH1_weight (f f1 : C(AddCircle L, ℂ))
    (hf : ∀ x : ℝ, HasDerivAt (fun y : ℝ => f (y : AddCircle L)) (f1 (x : AddCircle L)) x) :
    HasSum (fun n : ℤ => ‖(Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2) : ℂ) *
      fourierCoeff f n‖ ^ 2)
      ((∫ x : AddCircle L, ‖f x‖ ^ 2 ∂haarAddCircle) +
        ∫ x : AddCircle L, ‖f1 x‖ ^ 2 ∂haarAddCircle) := by
  have hs (g : C(AddCircle L, ℂ)) : HasSum (fun n : ℤ => ‖fourierCoeff g n‖ ^ 2)
      (∫ x : AddCircle L, ‖g x‖ ^ 2 ∂haarAddCircle) := by
    have hae := ContinuousMap.coeFn_toLp (p := 2) haarAddCircle (𝕜 := ℂ) g
    have hi : (∫ x : AddCircle L, ‖ContinuousMap.toLp 2 haarAddCircle ℂ g x‖ ^ 2 ∂haarAddCircle) =
        ∫ x : AddCircle L, ‖g x‖ ^ 2 ∂haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [hae] with x hx
      rw [hx]
    simpa only [fourierCoeff_congr_ae hae, hi] using
      hasSum_sq_fourierCoeff (ContinuousMap.toLp 2 haarAddCircle ℂ g)
  have hterm (n : ℤ) :
      ‖(Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2) : ℂ) * fourierCoeff f n‖ ^ 2 =
        ‖fourierCoeff f n‖ ^ 2 + ‖fourierCoeff f1 n‖ ^ 2 := by
    rw [fourierCoeff_circle_derivative f f1 hf]
    simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, sq_abs,
      Real.sq_sqrt (by positivity : 0 ≤ 1 + (2 * Real.pi * (n : ℝ) / L) ^ 2)]
    ring
  simpa only [hterm] using (hs f).add (hs f1)

noncomputable def periodicH1Coordinates (f f1 : C(AddCircle L, ℂ))
    (hf : ∀ x : ℝ, HasDerivAt (fun y : ℝ => f (y : AddCircle L)) (f1 (x : AddCircle L)) x) :
    lp (fun _ : ℤ => ℂ) 2 :=
  ⟨fun n => (Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2) : ℂ) * fourierCoeff f n, by
    change Memℓp (fun n : ℤ =>
      (Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2) : ℂ) * fourierCoeff f n) 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)]
    simpa using (hasSum_periodicH1_weight f f1 hf).summable⟩

theorem periodicH1Coordinates_norm_sq (f f1 : C(AddCircle L, ℂ))
    (hf : ∀ x : ℝ, HasDerivAt (fun y : ℝ => f (y : AddCircle L)) (f1 (x : AddCircle L)) x) :
    ‖periodicH1Coordinates f f1 hf‖ ^ 2 =
      (∫ x : AddCircle L, ‖f x‖ ^ 2 ∂haarAddCircle) +
        ∫ x : AddCircle L, ‖f1 x‖ ^ 2 ∂haarAddCircle := by
  have hs : HasSum (fun n : ℤ => ‖periodicH1Coordinates f f1 hf n‖ ^ 2)
      (‖periodicH1Coordinates f f1 hf‖ ^ 2) := by
    simpa using lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal)
      (periodicH1Coordinates f f1 hf)
  exact hs.unique (hasSum_periodicH1_weight f f1 hf)

theorem periodicH1Coordinates_reconstruct (f f1 : C(AddCircle L, ℂ))
    (hf : ∀ x : ℝ, HasDerivAt (fun y : ℝ => f (y : AddCircle L)) (f1 (x : AddCircle L)) x) :
    periodicSobolevJet (L := L) 0 0 (by omega) (periodicH1Coordinates f f1 hf) = f := by
  apply weightedFourier_eq_of_coeff
  intro n
  have hr : (Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by positivity :
      0 < 1 + (2 * Real.pi * (n : ℝ) / L) ^ 2))
  change periodicSobolevMoment L 0 0 n *
    ((Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2) : ℂ) * fourierCoeff f n) = _
  simp only [periodicSobolevMoment, pow_zero, zero_add, pow_one, one_div]
  rw [← mul_assoc, inv_mul_cancel₀ hr, one_mul]

end PoincareConjecture.M63
