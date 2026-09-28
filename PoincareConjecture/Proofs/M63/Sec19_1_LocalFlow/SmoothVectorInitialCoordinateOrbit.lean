import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.SmoothInitialCoordinateOrbit
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.VectorPeriodicInitialCoordinates

set_option autoImplicit false

open AddCircle PoincareConjecture.SpectralHeatNative
open scoped ContDiff

namespace PoincareConjecture.M63

theorem exists_smooth_vectorPeriodic_initialCoordinate_orbit
    {L : ℝ} [Fact (0 < L)] {ι : Type*} [Fintype ι]
    (f : C(AddCircle L, ι → ℝ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => f (x : AddCircle L))) :
    let fi : ι → C(AddCircle L, ℝ) := fun i =>
      (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).compLeftContinuous ℝ (AddCircle L) f
    ∃ w : ℝ → State ((ℤ × Fin 2) × ι), ContDiff ℝ ∞ w ∧ ∀ a : ℝ,
      (∀ i (n : ℤ), complexLpRealEquiv.symm (lpFinitePiEquiv ℝ (w a) i) n =
        ((1 + (2 * Real.pi * (n : ℝ) / L) ^ 2 : ℝ) : ℂ) *
          fourierCoeff (Complex.ofRealCLM.compLeftContinuous ℝ (AddCircle L)
            (periodicTranslation a (fi i))) n) ∧
      vectorPeriodicJet (L := L) 1 0 (by omega) (w a) = periodicTranslation a f ∧
      vectorPeriodicJet (L := L) 0 0 (by omega)
        (shiftedBaseMultiplier (fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1) (w a)) =
          periodicTranslation a f := by
  classical
  let fi : ι → C(AddCircle L, ℝ) := fun i =>
    (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).compLeftContinuous ℝ (AddCircle L) f
  have hfi (i : ι) : ContDiff ℝ ∞ (fun x : ℝ => fi i (x : AddCircle L)) :=
    (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).contDiff.comp hf
  choose w hw hrec using fun i => exists_smooth_realPeriodic_initialCoordinate_orbit (fi i) (hfi i)
  let W : ℝ → State ((ℤ × Fin 2) × ι) := fun a => (lpFinitePiEquiv ℝ).symm (fun i => w i a)
  have hW : ContDiff ℝ ∞ W :=
    (lpFinitePiEquiv (α := ℤ × Fin 2) (ι := ι) (E := ℝ) ℝ).symm.contDiff.comp
    (contDiff_pi.mpr hw)
  refine ⟨W, hW, ?_⟩
  intro a
  refine ⟨?_, ?_, ?_⟩
  · intro i n
    simpa only [W, ContinuousLinearEquiv.apply_symm_apply] using (hrec i a).1 n
  · ext x i
    change realPeriodicJet (L := L) 1 0 (by omega)
      (lpFinitePiEquiv ℝ ((lpFinitePiEquiv ℝ).symm (fun i => w i a)) i) x = _
    rw [ContinuousLinearEquiv.apply_symm_apply, (hrec i a).2.1]
    rfl
  · have hsplit (u : State ((ℤ × Fin 2) × ι)) (i : ι) :
        lpFinitePiEquiv ℝ
            (shiftedBaseMultiplier (fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1) u) i =
          shiftedBaseMultiplier (periodicSpectrum L) (lpFinitePiEquiv ℝ u i) := by
      apply lp.ext
      funext p
      rfl
    ext x i
    change realPeriodicJet (L := L) 0 0 (by omega)
      (lpFinitePiEquiv ℝ
        (shiftedBaseMultiplier (fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1)
          ((lpFinitePiEquiv ℝ).symm (fun i => w i a))) i) x = _
    rw [hsplit, ContinuousLinearEquiv.apply_symm_apply, (hrec i a).2.2]
    rfl

end PoincareConjecture.M63
