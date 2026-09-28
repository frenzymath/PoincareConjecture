import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.SmoothVectorInitialCoordinateOrbit
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.VectorSpectralTranslation
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicFourierTranslation

set_option autoImplicit false

open AddCircle PoincareConjecture.SpectralHeatNative
open scoped ContDiff

namespace PoincareConjecture.M63

theorem exists_smooth_vectorPeriodic_spectral_initial_state
    {L : ℝ} [Fact (0 < L)] {ι : Type*} [Fintype ι]
    (f : C(AddCircle L, ι → ℝ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => f (x : AddCircle L))) :
    let fi : ι → C(AddCircle L, ℝ) := fun i =>
      (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).compLeftContinuous ℝ (AddCircle L) f
    ∃ w : State ((ℤ × Fin 2) × ι),
      (∀ i (n : ℤ), complexLpRealEquiv.symm (lpFinitePiEquiv ℝ w i) n =
        ((1 + (2 * Real.pi * (n : ℝ) / L) ^ 2 : ℝ) : ℂ) *
          fourierCoeff (Complex.ofRealCLM.compLeftContinuous ℝ (AddCircle L) (fi i)) n) ∧
      vectorPeriodicJet (L := L) 1 0 (by omega) w = f ∧
      vectorPeriodicJet (L := L) 0 0 (by omega)
        (shiftedBaseMultiplier (fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1) w) = f ∧
      ContDiff ℝ ∞ (fun s : ℝ => vectorPeriodicSpectralTranslation (L := L) s w) := by
  classical
  dsimp only
  let fi : ι → C(AddCircle L, ℝ) := fun i =>
    (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).compLeftContinuous ℝ (AddCircle L) f
  let A := Complex.ofRealCLM.compLeftContinuous ℝ (AddCircle L)
  obtain ⟨W, hW, hrec⟩ := exists_smooth_vectorPeriodic_initialCoordinate_orbit f hf
  have hz (g : C(AddCircle L, ℝ)) : periodicTranslation 0 g = g := by
    ext x
    change g (x - (0 : AddCircle L)) = g x
    rw [sub_zero]
  have hzv : periodicTranslation 0 f = f := by
    apply ContinuousMap.ext
    intro x
    change f (x - (0 : AddCircle L)) = f x
    rw [sub_zero]
  have hcoeff (i : ι) (n : ℤ) :
      complexLpRealEquiv.symm (lpFinitePiEquiv ℝ (W 0) i) n =
        ((1 + (2 * Real.pi * (n : ℝ) / L) ^ 2 : ℝ) : ℂ) * fourierCoeff (A (fi i)) n := by
    simpa only [hz] using (hrec 0).1 i n
  have horbit (s : ℝ) : W s = vectorPeriodicSpectralTranslation (L := L) s (W 0) := by
    apply (lpFinitePiEquiv (α := ℤ × Fin 2) (ι := ι) (E := ℝ) ℝ).injective
    funext i
    apply complexLpRealEquiv.symm.injective
    rw [(vectorPeriodicSpectralTranslation_spec s (W 0)).1 i,
      (realPeriodicSpectralTranslation_spec s _).1]
    apply lp.ext
    funext n
    rw [(hrec s).1 i n, (periodicSpectralTranslation_spec s _).1 n, hcoeff]
    have hshift : fourierCoeff (A (periodicTranslation s (fi i))) n =
        fourier n (-(s : AddCircle L)) * fourierCoeff (A (fi i)) n := by
      change fourierCoeff (fun x => A (fi i) (x - (s : AddCircle L))) n = _
      simpa only [smul_eq_mul] using fourierCoeff_sub_const (A (fi i)) s n
    change ((1 + (2 * Real.pi * (n : ℝ) / L) ^ 2 : ℝ) : ℂ) *
      fourierCoeff (A (periodicTranslation s (fi i))) n = _
    rw [hshift]
    ring
  refine ⟨W 0, hcoeff, ?_, ?_, ?_⟩
  · simpa only [hzv] using (hrec 0).2.1
  · simpa only [hzv] using (hrec 0).2.2
  · have heq : (fun s : ℝ => vectorPeriodicSpectralTranslation (L := L) s (W 0)) = W :=
      funext (fun s => (horbit s).symm)
    rw [heq]
    exact hW

end PoincareConjecture.M63
