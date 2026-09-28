import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.InitialForcingTranslation
import Mathlib.Topology.CompactOpen

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture.M63

open SpectralHeatNative

variable {L : ℝ} {ι : Type*} [Fintype ι]

local notation "S" => State ((ℤ × Fin 2) × ι)
local notation "H" => lp (fun _ : ℤ => ℂ) 2
local notation "lambda" => (fun p : (ℤ × Fin 2) × ι => periodicSpectrum L (Prod.fst p))

theorem eventually_initialBranch_spectralTranslation
    (M : H →L[ℝ] S →L[ℝ] S) (G : ℝ × S → H) (Q : ℝ × S → S)
    (hM : ∀ s c v, vectorPeriodicSpectralTranslation (L := L) s (M c v) =
      M (periodicSpectralTranslation (L := L) s c)
        (vectorPeriodicSpectralTranslation (L := L) s v))
    {O : Set (ℝ × S)} (hO : IsOpen O)
    (hcoeff : ∀ s t v, 0 ≤ t → (t, v) ∈ O →
      (t, vectorPeriodicSpectralTranslation (L := L) s v) ∈ O →
      G (t, vectorPeriodicSpectralTranslation (L := L) s v) =
          periodicSpectralTranslation (L := L) s (G (t, v)) ∧
        Q (t, vectorPeriodicSpectralTranslation (L := L) s v) =
          vectorPeriodicSpectralTranslation (L := L) s (Q (t, v)))
    {T : ℝ} (hT : 0 ≤ T) (w : S) (F : ForcingSpace ((ℤ × Fin 2) × ι) T)
    (u : S → ForcingSpace ((ℤ × Fin 2) × ι) T)
    (heq : ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T,
      F t = M (G (t, initialResponseTrace lambda w hT F ⟨t, ht⟩))
          (initialHeatHigh lambda w t + shiftedHighOperator hT lambda F t -
            shiftedBaseMultiplier lambda (initialResponseTrace lambda w hT F ⟨t, ht⟩)) +
        Q (t, initialResponseTrace lambda w hT F ⟨t, ht⟩))
    (hunique : ∀ᶠ z : S × ForcingSpace ((ℤ × Fin 2) × ι) T in 𝓝 (w, F),
      (∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T,
        z.2 t = M (G (t, initialResponseTrace lambda z.1 hT z.2 ⟨t, ht⟩))
            (initialHeatHigh lambda z.1 t + shiftedHighOperator hT lambda z.2 t -
              shiftedBaseMultiplier lambda (initialResponseTrace lambda z.1 hT z.2 ⟨t, ht⟩)) +
          Q (t, initialResponseTrace lambda z.1 hT z.2 ⟨t, ht⟩)) ↔ u z.1 = z.2)
    (hinside : ∀ t : Icc (0 : ℝ) T,
      ((t : ℝ), initialResponseTrace lambda w hT F t) ∈ O) :
    ∀ᶠ s : ℝ in 𝓝 0,
      u (vectorPeriodicSpectralTranslation (L := L) s w) =
        (vectorPeriodicSpectralTranslation (L := L) s).compLpL 2 (timeMeasure T) F := by
  let V := initialResponseTrace lambda w hT F
  let K : ℝ → C(Icc (0 : ℝ) T, ℝ × S) := fun s =>
    ⟨fun t => ((t : ℝ), vectorPeriodicSpectralTranslation (L := L) s (V t)),
      continuous_subtype_val.prodMk
        ((vectorPeriodicSpectralTranslation (L := L) s).continuous.comp V.continuous)⟩
  have hK : Continuous K := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    have harg : Continuous (fun z : ℝ × Icc (0 : ℝ) T => (z.1, V z.2)) :=
      continuous_fst.prodMk (V.continuous.comp continuous_snd)
    have hshift := (continuous_vectorPeriodicSpectralTranslation (L := L) (ι := ι)).comp harg
    exact (continuous_subtype_val.comp continuous_snd).prodMk
      hshift
  have hdomain : ∀ᶠ s : ℝ in 𝓝 0, ∀ t : Icc (0 : ℝ) T,
      ((t : ℝ), vectorPeriodicSpectralTranslation (L := L) s (V t)) ∈ O := by
    have hN : K ⁻¹' {f : C(Icc (0 : ℝ) T, ℝ × S) | MapsTo f univ O} ∈ 𝓝 0 :=
      ((ContinuousMap.isOpen_setOfPred_mapsTo isCompact_univ hO).preimage hK).mem_nhds
        (by
          intro t _
          change ((t : ℝ), vectorPeriodicSpectralTranslation (L := L) 0 (V t)) ∈ O
          simpa only [vectorPeriodicSpectralTranslation_zero,
            ContinuousLinearMap.id_apply] using hinside t)
    filter_upwards [hN] with s hs
    exact fun t => hs (mem_univ t)
  have hwarg : Continuous (fun s : ℝ => (s, w)) :=
    continuous_id.prodMk continuous_const
  have hFarg : Continuous (fun s : ℝ => (s, F)) :=
    continuous_id.prodMk continuous_const
  have hwcont :=
    (continuous_vectorPeriodicSpectralTranslation (L := L) (ι := ι)).comp hwarg
  have hFcont := (continuous_vectorPeriodicSpectralTranslation_compLpL
    (L := L) (ι := ι) (timeMeasure T)).comp hFarg
  have hpair := hwcont.prodMk hFcont
  have hlim : Tendsto (fun s : ℝ =>
      (vectorPeriodicSpectralTranslation (L := L) s w,
        (vectorPeriodicSpectralTranslation (L := L) s).compLpL 2 (timeMeasure T) F))
      (𝓝 0) (𝓝 (w, F)) := by
    have h := hpair.continuousAt.tendsto (x := 0)
    simp only [Function.comp_def] at h
    rw [vectorPeriodicSpectralTranslation_compLpL_zero,
      vectorPeriodicSpectralTranslation_zero, ContinuousLinearMap.id_apply] at h
    exact h
  filter_upwards [hdomain, hlim.eventually hunique] with s hs hu
  exact hu.mp (initial_forcing_equation_spectralTranslation M G Q hM hcoeff hT w F heq s
    hinside hs)

end PoincareConjecture.M63
