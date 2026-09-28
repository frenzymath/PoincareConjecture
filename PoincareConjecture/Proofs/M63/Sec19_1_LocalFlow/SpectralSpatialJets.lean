import PoincareConjecture.Proofs.M63.Mathlib.TranslationOrbitJets
import PoincareConjecture.Proofs.M63.Mathlib.CompactPathComposition
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.SmoothSpectralTraceOrbit









set_option autoImplicit false

open Set
open scoped ContDiff

namespace PoincareConjecture.M63

open SpectralHeatNative





theorem initialResponseTrace_spatial_jets
    {L : ℝ} [Fact (0 < L)] {ι : Type*} [Fintype ι] {T : ℝ} (hT : 0 ≤ T)
    (w : State ((ℤ × Fin 2) × ι)) (F : ForcingSpace ((ℤ × Fin 2) × ι) T) :
    let lambda := fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1
    let V := initialResponseTrace lambda w hT F
    ContDiffAt ℝ ∞ (fun s : ℝ => initialResponseTrace lambda
      (vectorPeriodicSpectralTranslation (L := L) s w) hT
      ((vectorPeriodicSpectralTranslation (L := L) s).compLpL 2 (timeMeasure T) F)) 0 →
    (∀ t : Icc (0 : ℝ) T, ContDiff ℝ ∞ (fun x : ℝ =>
      vectorPeriodicJet (L := L) 1 0 (by omega) (V t) (x : AddCircle L))) ∧
      ∀ k : ℕ, ∃ J : C(Icc (0 : ℝ) T, C(AddCircle L, ι → ℝ)),
        ∀ (t : Icc (0 : ℝ) T) (x : ℝ),
          iteratedDeriv k (fun y : ℝ =>
            vectorPeriodicJet (L := L) 1 0 (by omega) (V t) (y : AddCircle L)) x =
              J t (x : AddCircle L) := by
  dsimp only
  intro horbit
  let lambda := fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1
  let V := initialResponseTrace lambda w hT F
  let U := fun s : ℝ => initialResponseTrace lambda
    (vectorPeriodicSpectralTranslation (L := L) s w) hT
    ((vectorPeriodicSpectralTranslation (L := L) s).compLpL 2 (timeMeasure T) F)
  let D := vectorPeriodicJet (L := L) (ι := ι) 1 0 (by omega)
  let P : C(Icc (0 : ℝ) T, State ((ℤ × Fin 2) × ι)) →L[ℝ]
      C(Icc (0 : ℝ) T, C(AddCircle L, ι → ℝ)) :=
    D.compLeftContinuous ℝ (Icc (0 : ℝ) T)
  have hP : ContDiff ℝ ∞
      (fun v : C(Icc (0 : ℝ) T, State ((ℤ × Fin 2) × ι)) => P v) := by
    exact contDiff_postcomp_independent_universes (Icc (0 : ℝ) T)
      ⟨D, D.continuous⟩ D.contDiff
  have horbit' : ContDiffAt ℝ ∞ U 0 := horbit
  have hcomp := hP.contDiffAt.comp 0 horbit'
  have hU : ContDiffAt ℝ ∞ (fun s : ℝ => P (U s)) 0 := hcomp
  apply spatial_jets_of_smooth_translation_orbit (P V) (fun s => P (U s)) hU
  intro s t x
  have htrace : U s t = vectorPeriodicSpectralTranslation (L := L) s (V t) :=
    vectorPeriodicSpectralTranslation_initialResponseTrace (L := L) hT w F s t
  change D (U s t) x = D (V t) (x - (s : AddCircle L))
  rw [htrace]
  change vectorPeriodicJet (L := L) 1 0 (by omega)
    (vectorPeriodicSpectralTranslation (L := L) s (V t)) x = _
  rw [vectorPeriodicJet_spectralTranslation]
  rfl

end PoincareConjecture.M63
