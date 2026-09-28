import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.PeriodicInitialCoordinates
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicH1Coordinates

set_option autoImplicit false

open AddCircle PoincareConjecture.SpectralHeatNative
open scoped ContDiff

namespace PoincareConjecture.M63

variable {L : ℝ} [Fact (0 < L)]

noncomputable def realPeriodicH2Encode :
    (C(AddCircle L, ℝ) × C(AddCircle L, ℝ)) →L[ℝ] State (ℤ × Fin 2) :=
  complexLpRealEquiv.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (fourierBasis.repr.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ |>.comp
      ((ContinuousMap.toLp 2 haarAddCircle ℂ).restrictScalars ℝ |>.comp
        ((Complex.ofRealCLM.compLeftContinuous ℝ (AddCircle L)).comp
          (ContinuousLinearMap.fst ℝ _ _ - ContinuousLinearMap.snd ℝ _ _))))

theorem realPeriodicH2Encode_spec (f f1 f2 : C(AddCircle L, ℝ))
    (h1 : ∀ x : ℝ, HasDerivAt (fun y : ℝ => f (y : AddCircle L)) (f1 (x : AddCircle L)) x)
    (h2 : ∀ x : ℝ, HasDerivAt (fun y : ℝ => f1 (y : AddCircle L)) (f2 (x : AddCircle L)) x) :
    (∀ n : ℤ, complexLpRealEquiv.symm (realPeriodicH2Encode (f, f2)) n =
      ((1 + (2 * Real.pi * (n : ℝ) / L) ^ 2 : ℝ) : ℂ) *
        fourierCoeff (Complex.ofRealCLM.compLeftContinuous ℝ (AddCircle L) f) n) ∧
    realPeriodicJet (L := L) 1 0 (by omega) (realPeriodicH2Encode (f, f2)) = f ∧
    realPeriodicJet (L := L) 0 0 (by omega)
      (shiftedBaseMultiplier (periodicSpectrum L) (realPeriodicH2Encode (f, f2))) = f := by
  let A := Complex.ofRealCLM.compLeftContinuous ℝ (AddCircle L)
  have hc1 (x : ℝ) : HasDerivAt (fun y : ℝ => A f (y : AddCircle L))
      (A f1 (x : AddCircle L)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x (h1 x)
  have hc2 (x : ℝ) : HasDerivAt (fun y : ℝ => A f1 (y : AddCircle L))
      (A f2 (x : AddCircle L)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x (h2 x)
  have hcoeff (n : ℤ) : complexLpRealEquiv.symm (realPeriodicH2Encode (f, f2)) n =
      ((1 + (2 * Real.pi * (n : ℝ) / L) ^ 2 : ℝ) : ℂ) * fourierCoeff (A f) n := by
    change complexLpRealEquiv.symm (complexLpRealEquiv
      (fourierBasis.repr (ContinuousMap.toLp 2 haarAddCircle ℂ (A (f - f2))))) n = _
    simp only [LinearIsometryEquiv.symm_apply_apply, map_sub, lp.coeFn_sub, Pi.sub_apply]
    rw [fourierBasis_repr, fourierBasis_repr, fourierCoeff_toLp, fourierCoeff_toLp,
      fourierCoeff_circle_derivative (A f1) (A f2) hc2,
      fourierCoeff_circle_derivative (A f) (A f1) hc1]
    push_cast
    linear_combination -(fourierCoeff (A f) n *
      (2 * (Real.pi : ℂ) * n / (L : ℂ)) ^ 2) * Complex.I_sq
  have heq1 : deriv (fun x : ℝ => f (x : AddCircle L)) =
      fun x : ℝ => f1 (x : AddCircle L) := funext (fun x => (h1 x).deriv)
  have heq2 : deriv (fun x : ℝ => f1 (x : AddCircle L)) =
      fun x : ℝ => f2 (x : AddCircle L) := funext (fun x => (h2 x).deriv)
  have hf : ContDiff ℝ 2 (fun x : ℝ => f (x : AddCircle L)) := by
    rw [show (2 : ℕ∞ω) = 1 + 1 by norm_num, contDiff_succ_iff_deriv]
    refine ⟨fun x => (h1 x).differentiableAt, by norm_num, ?_⟩
    rw [heq1, contDiff_one_iff_deriv]
    refine ⟨fun x => (h2 x).differentiableAt, ?_⟩
    rw [heq2]
    exact f2.continuous.comp (AddCircle.continuous_mk' L)
  obtain ⟨w, hw, hrec, hrec0⟩ := exists_realPeriodic_initialCoordinates f hf
  have henc : realPeriodicH2Encode (f, f2) = w := by
    apply complexLpRealEquiv.symm.injective
    apply lp.ext
    funext n
    exact (hcoeff n).trans (hw n).symm
  exact ⟨hcoeff, henc ▸ hrec, henc ▸ hrec0⟩

end PoincareConjecture.M63
