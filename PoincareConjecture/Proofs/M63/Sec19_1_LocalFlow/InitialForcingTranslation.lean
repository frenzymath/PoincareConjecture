import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.NonlinearSpectralTranslation
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.VectorSpectralResponse

set_option autoImplicit false

open Set Filter MeasureTheory

namespace PoincareConjecture.M63

open SpectralHeatNative

variable {L : ℝ} {ι : Type*} [Fintype ι]

local notation "S" => State ((ℤ × Fin 2) × ι)
local notation "H" => lp (fun _ : ℤ => ℂ) 2
local notation "lambda" => (fun p : (ℤ × Fin 2) × ι => periodicSpectrum L (Prod.fst p))

theorem initial_forcing_equation_spectralTranslation
    (M : H →L[ℝ] S →L[ℝ] S) (G : ℝ × S → H) (Q : ℝ × S → S)
    (hM : ∀ s c u, vectorPeriodicSpectralTranslation (L := L) s (M c u) =
      M (periodicSpectralTranslation (L := L) s c)
        (vectorPeriodicSpectralTranslation (L := L) s u))
    {O : Set (ℝ × S)}
    (hcoeff : ∀ s t u, 0 ≤ t → (t, u) ∈ O →
      (t, vectorPeriodicSpectralTranslation (L := L) s u) ∈ O →
      G (t, vectorPeriodicSpectralTranslation (L := L) s u) =
          periodicSpectralTranslation (L := L) s (G (t, u)) ∧
        Q (t, vectorPeriodicSpectralTranslation (L := L) s u) =
          vectorPeriodicSpectralTranslation (L := L) s (Q (t, u)))
    {T : ℝ} (hT : 0 ≤ T) (w : S) (F : ForcingSpace ((ℤ × Fin 2) × ι) T)
    (heq : ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T,
      F t = M (G (t, initialResponseTrace lambda w hT F ⟨t, ht⟩))
          (initialHeatHigh lambda w t + shiftedHighOperator hT lambda F t -
            shiftedBaseMultiplier lambda (initialResponseTrace lambda w hT F ⟨t, ht⟩)) +
        Q (t, initialResponseTrace lambda w hT F ⟨t, ht⟩))
    (s : ℝ)
    (hinside : ∀ t : Icc (0 : ℝ) T,
      ((t : ℝ), initialResponseTrace lambda w hT F t) ∈ O)
    (htranslated : ∀ t : Icc (0 : ℝ) T,
      ((t : ℝ), vectorPeriodicSpectralTranslation (L := L) s
        (initialResponseTrace lambda w hT F t)) ∈ O) :
    ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T,
      ((vectorPeriodicSpectralTranslation (L := L) s).compLpL 2 (timeMeasure T) F) t =
        M (G (t, initialResponseTrace lambda
            (vectorPeriodicSpectralTranslation (L := L) s w) hT
            ((vectorPeriodicSpectralTranslation (L := L) s).compLpL 2 (timeMeasure T) F)
              ⟨t, ht⟩))
          (initialHeatHigh lambda (vectorPeriodicSpectralTranslation (L := L) s w) t +
            shiftedHighOperator hT lambda
              ((vectorPeriodicSpectralTranslation (L := L) s).compLpL 2 (timeMeasure T) F) t -
            shiftedBaseMultiplier lambda (initialResponseTrace lambda
              (vectorPeriodicSpectralTranslation (L := L) s w) hT
              ((vectorPeriodicSpectralTranslation (L := L) s).compLpL 2 (timeMeasure T) F)
                ⟨t, ht⟩)) +
          Q (t, initialResponseTrace lambda (vectorPeriodicSpectralTranslation (L := L) s w) hT
            ((vectorPeriodicSpectralTranslation (L := L) s).compLpL 2 (timeMeasure T) F)
              ⟨t, ht⟩) := by
  filter_upwards [heq,
    (vectorPeriodicSpectralTranslation (L := L) s).coeFn_compLpL F,
    vectorPeriodicSpectralTranslation_shiftedHigh (L := L) hT F s,
    ae_restrict_mem measurableSet_Ioc] with t heqt hact hhigh htime
  intro ht
  have hc := hcoeff s t (initialResponseTrace lambda w hT F ⟨t, ht⟩)
    ht.1 (hinside ⟨t, ht⟩) (htranslated ⟨t, ht⟩)
  have htrace : initialResponseTrace lambda (vectorPeriodicSpectralTranslation (L := L) s w)
      hT ((vectorPeriodicSpectralTranslation (L := L) s).compLpL 2 (timeMeasure T) F)
        ⟨t, ht⟩ =
      vectorPeriodicSpectralTranslation (L := L) s
        (initialResponseTrace lambda w hT F ⟨t, ht⟩) :=
    vectorPeriodicSpectralTranslation_initialResponseTrace (L := L) hT w F s ⟨t, ht⟩
  have hheat : initialHeatHigh lambda (vectorPeriodicSpectralTranslation (L := L) s w) t =
      vectorPeriodicSpectralTranslation (L := L) s (initialHeatHigh lambda w t) :=
    vectorPeriodicSpectralTranslation_initialHeatHigh (L := L) w s htime.1
  have hJ (v : S) : vectorPeriodicSpectralTranslation (L := L) s
      (shiftedBaseMultiplier lambda v) =
      shiftedBaseMultiplier lambda (vectorPeriodicSpectralTranslation (L := L) s v) :=
    vectorPeriodicSpectralTranslation_shiftedBaseMultiplier (L := L) v s
  change shiftedHighOperator hT lambda
      ((vectorPeriodicSpectralTranslation (L := L) s).compLpL 2 (timeMeasure T) F) t =
      vectorPeriodicSpectralTranslation (L := L) s (shiftedHighOperator hT lambda F t)
    at hhigh
  rw [hact, heqt ht, map_add, hM, htrace, hc.1, hc.2, hheat, hhigh,
    ← hJ, ← map_add, ← map_sub]

end PoincareConjecture.M63
