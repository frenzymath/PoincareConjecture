import PoincareConjecture.Proofs.M63.Mathlib.PeriodicH1Coordinates










set_option autoImplicit false

open AddCircle MeasureTheory
open scoped ENNReal

namespace PoincareConjecture.M63

variable {L : ℝ} [Fact (0 < L)]




theorem fourierCoeff_weightedFourier (w u : lp (fun _ : ℤ => ℂ) 2) (n : ℤ) :
    fourierCoeff (weightedFourier (L := L) w u) n = w n * u n := by
  classical
  let A : C(AddCircle L, ℂ) →L[ℂ] ℂ :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).comp
      (fourierBasis.repr.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (ContinuousMap.toLp 2 haarAddCircle ℂ))
  have hA (f : C(AddCircle L, ℂ)) : A f = fourierCoeff f n := by
    change fourierBasis.repr (ContinuousMap.toLp 2 haarAddCircle ℂ f) n = _
    rw [fourierBasis_repr,
      fourierCoeff_congr_ae (ContinuousMap.coeFn_toLp (p := 2) haarAddCircle (𝕜 := ℂ) f)]
  have hmode (m : ℤ) : A ((w m * u m) • fourier m) =
      if m = n then w n * u n else 0 := by
    rw [map_smul, hA, fourierCoeff_fourier]
    by_cases hm : m = n
    · subst m
      simp
    · simp [hm, Ne.symm hm]
  have hs := A.hasSum (weightedFourier_hasSum (L := L) w u)
  simp_rw [hmode, hA] at hs
  exact hs.unique (hasSum_ite_eq n (w n * u n))




theorem periodicH1Decoder_injective :
    Function.Injective (periodicSobolevJet (L := L) 0 0 (by omega)) := by
  intro u v huv
  apply lp.ext
  funext n
  have h := congrArg (fun f : C(AddCircle L, ℂ) => fourierCoeff f n) huv
  change fourierCoeff (weightedFourier _ u) n = fourierCoeff (weightedFourier _ v) n at h
  rw [fourierCoeff_weightedFourier, fourierCoeff_weightedFourier] at h
  have hw : periodicSobolevMoment L 0 0 n ≠ 0 := by
    have hr : (Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by positivity :
        0 < 1 + (2 * Real.pi * (n : ℝ) / L) ^ 2))
    simpa only [periodicSobolevMoment, pow_zero, zero_add, pow_one] using one_div_ne_zero hr
  exact mul_left_cancel₀ hw h




theorem periodicH1Decoder_norm_sq (u : lp (fun _ : ℤ => ℂ) 2) (g : C(AddCircle L, ℂ))
    (hu : ∀ x : ℝ, HasDerivAt
      (fun y : ℝ => periodicSobolevJet (L := L) 0 0 (by omega) u (y : AddCircle L))
      (g (x : AddCircle L)) x) :
    ‖u‖ ^ 2 = (∫ x : AddCircle L, ‖periodicSobolevJet (L := L) 0 0 (by omega) u x‖ ^ 2
      ∂haarAddCircle) + ∫ x : AddCircle L, ‖g x‖ ^ 2 ∂haarAddCircle := by
  have heq : periodicH1Coordinates (periodicSobolevJet (L := L) 0 0 (by omega) u) g hu = u :=
    periodicH1Decoder_injective (periodicH1Coordinates_reconstruct _ g hu)
  have h := periodicH1Coordinates_norm_sq (periodicSobolevJet (L := L) 0 0 (by omega) u) g hu
  rw [heq] at h
  exact h

end PoincareConjecture.M63
