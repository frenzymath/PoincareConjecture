import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.RealPeriodicJets
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicCircleTrace










set_option autoImplicit false

open AddCircle PoincareConjecture.SpectralHeatNative
open scoped ENNReal

namespace PoincareConjecture.M63





theorem exists_realPeriodic_initialCoordinates {L : ℝ} [Fact (0 < L)]
    (f : C(AddCircle L, ℝ)) (hf : ContDiff ℝ 2 (fun x : ℝ => f (x : AddCircle L))) :
    ∃ w : State (ℤ × Fin 2),
      (∀ n : ℤ, complexLpRealEquiv.symm w n =
        ((1 + (2 * Real.pi * (n : ℝ) / L) ^ 2 : ℝ) : ℂ) *
          fourierCoeff (Complex.ofRealCLM.compLeftContinuous ℝ (AddCircle L) f) n) ∧
      realPeriodicJet (L := L) 1 0 (by omega) w = f ∧
      realPeriodicJet (L := L) 0 0 (by omega)
        (shiftedBaseMultiplier (periodicSpectrum L) w) = f := by
  let fc : C(AddCircle L, ℂ) :=
    Complex.ofRealCLM.compLeftContinuous ℝ (AddCircle L) f
  have hfc : ContDiff ℝ 2 (fun x : ℝ => fc (x : AddCircle L)) :=
    Complex.ofRealCLM.contDiff.comp hf
  let z : lp (fun _ : ℤ => ℂ) 2 :=
    ⟨fun n : ℤ => ((1 + (2 * Real.pi * (n : ℝ) / L) ^ 2 : ℝ) : ℂ) *
      fourierCoeff fc n, memℓp_second_weight_circle fc hfc⟩
  have hrec : periodicSobolevJet (L := L) 1 0 (by omega) z = fc := by
    apply weightedFourier_eq_of_coeff
    intro n
    change periodicSobolevMoment L 1 0 n *
      (((1 + (2 * Real.pi * (n : ℝ) / L) ^ 2 : ℝ) : ℂ) * fourierCoeff fc n) = _
    have hpos : 0 < 1 + (2 * Real.pi * (n : ℝ) / L) ^ 2 := by positivity
    have hroot : (Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2) : ℂ) ^ 2 =
        ((1 + (2 * Real.pi * (n : ℝ) / L) ^ 2 : ℝ) : ℂ) := by
      exact_mod_cast Real.sq_sqrt hpos.le
    have hne : ((1 + (2 * Real.pi * (n : ℝ) / L) ^ 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hpos.ne'
    simp only [periodicSobolevMoment, pow_zero, show 1 + 1 = (2 : ℕ) by omega, hroot]
    rw [one_div, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have hreal : realPeriodicJet (L := L) 1 0 (by omega) (complexLpRealEquiv z) = f := by
    change (Complex.reCLM.compLeftContinuous ℝ (AddCircle L))
      (periodicSobolevJet (L := L) 1 0 (by omega)
        (complexLpRealEquiv.symm (complexLpRealEquiv z))) = f
    rw [LinearIsometryEquiv.symm_apply_apply, hrec]
    ext x
    rfl
  refine ⟨complexLpRealEquiv z, ?_, hreal, ?_⟩
  · intro n
    rw [LinearIsometryEquiv.symm_apply_apply]
  · have hshift : shiftedBaseMultiplier (periodicSpectrum L) =
        scaleDecode (periodicSpectrum L) 1 := by
      ext u p
      change (1 / Real.sqrt (1 + (periodicSpectrum L p : ℝ))) * u p =
        (scaleWeight (periodicSpectrum L) 1 p)⁻¹ * u p
      simp only [scaleWeight, pow_one, one_div]
    rw [hshift, realPeriodicJet_scaleDecode]
    exact hreal

end PoincareConjecture.M63
