import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.InitialBranchTranslation
import Mathlib.Analysis.Calculus.ContDiff.Basic

set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

namespace PoincareConjecture.M63

open SpectralHeatNative

theorem contDiffAt_initialResponseTrace_spectral_orbit
    {L : ℝ} {ι : Type*} [Fintype ι] {T : ℝ} (hT : 0 ≤ T)
    (w : State ((ℤ × Fin 2) × ι)) (F : ForcingSpace ((ℤ × Fin 2) × ι) T)
    (u : State ((ℤ × Fin 2) × ι) → ForcingSpace ((ℤ × Fin 2) × ι) T)
    (htrace : ContDiffAt ℝ ∞ (fun w' => initialResponseTrace
      (fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1) w' hT (u w')) w)
    (hw : ContDiffAt ℝ ∞ (fun s : ℝ => vectorPeriodicSpectralTranslation (L := L) s w) 0)
    (hbranch : ∀ᶠ s : ℝ in 𝓝 0,
      u (vectorPeriodicSpectralTranslation (L := L) s w) =
        (vectorPeriodicSpectralTranslation (L := L) s).compLpL 2 (timeMeasure T) F) :
    ContDiffAt ℝ ∞ (fun s : ℝ => initialResponseTrace
      (fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1)
      (vectorPeriodicSpectralTranslation (L := L) s w) hT
      ((vectorPeriodicSpectralTranslation (L := L) s).compLpL 2 (timeMeasure T) F)) 0 := by
  have hw0 : vectorPeriodicSpectralTranslation (L := L) 0 w = w := by
    rw [vectorPeriodicSpectralTranslation_zero, ContinuousLinearMap.id_apply]
  rw [← hw0] at htrace
  have hcomp := htrace.comp 0 hw
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [hbranch] with s hs
  dsimp only [Function.comp_def]
  rw [hs]

end PoincareConjecture.M63
