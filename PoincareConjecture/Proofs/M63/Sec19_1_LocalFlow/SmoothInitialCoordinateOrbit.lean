import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.InitialCoordinateEncoder
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.PeriodicGaussianC2
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicTranslationSmoothness

set_option autoImplicit false

open AddCircle PoincareConjecture.SpectralHeatNative
open scoped ContDiff

namespace PoincareConjecture.M63

theorem exists_smooth_realPeriodic_initialCoordinate_orbit {L : ℝ} [Fact (0 < L)]
    (f : C(AddCircle L, ℝ)) (hf : ContDiff ℝ ∞ (fun x : ℝ => f (x : AddCircle L))) :
    ∃ w : ℝ → State (ℤ × Fin 2), ContDiff ℝ ∞ w ∧ ∀ a : ℝ,
      (∀ n : ℤ, complexLpRealEquiv.symm (w a) n =
        ((1 + (2 * Real.pi * (n : ℝ) / L) ^ 2 : ℝ) : ℂ) *
          fourierCoeff (Complex.ofRealCLM.compLeftContinuous ℝ (AddCircle L)
            (periodicTranslation a f)) n) ∧
      realPeriodicJet (L := L) 1 0 (by omega) (w a) = periodicTranslation a f ∧
      realPeriodicJet (L := L) 0 0 (by omega)
        (shiftedBaseMultiplier (periodicSpectrum L) (w a)) = periodicTranslation a f := by
  obtain ⟨f1, f2, h1, h2, _⟩ := exists_periodicGaussian_c2_jets f
    (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  have heq1 : (fun x : ℝ => f1 (x : AddCircle L)) =
      deriv (fun x : ℝ => f (x : AddCircle L)) := funext (fun x => (h1 x).deriv.symm)
  have heq2 : (fun x : ℝ => f2 (x : AddCircle L)) =
      deriv (deriv (fun x : ℝ => f (x : AddCircle L))) := by
    rw [← heq1]
    exact funext (fun x => (h2 x).deriv.symm)
  have hf2 : ContDiff ℝ ∞ (fun x : ℝ => f2 (x : AddCircle L)) := by
    rw [heq2]
    exact (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hf).2).2
  let w : ℝ → State (ℤ × Fin 2) := fun a =>
    realPeriodicH2Encode (periodicTranslation a f, periodicTranslation a f2)
  have hw := (realPeriodicH2Encode (L := L)).contDiff.comp
    ((contDiff_periodicTranslation f hf).prodMk (contDiff_periodicTranslation f2 hf2))
  refine ⟨w, hw, ?_⟩
  intro a
  apply realPeriodicH2Encode_spec (periodicTranslation a f) (periodicTranslation a f1)
    (periodicTranslation a f2)
  · intro x
    change HasDerivAt (fun y : ℝ => f ((y : AddCircle L) - (a : AddCircle L)))
      (f1 ((x : AddCircle L) - (a : AddCircle L))) x
    simpa only [Function.comp_def, id_eq, one_smul, AddCircle.coe_sub] using
      (h1 (x - a)).scomp x ((hasDerivAt_id x).sub_const a)
  · intro x
    change HasDerivAt (fun y : ℝ => f1 ((y : AddCircle L) - (a : AddCircle L)))
      (f2 ((x : AddCircle L) - (a : AddCircle L))) x
    simpa only [Function.comp_def, id_eq, one_smul, AddCircle.coe_sub] using
      (h2 (x - a)).scomp x ((hasDerivAt_id x).sub_const a)

end PoincareConjecture.M63
