import PoincareConjecture.Statements.M49VolumeLoss
import PoincareConjecture.Proofs.M50.Mathlib.FiniteCardBound

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

private theorem finite_of_finset_card_bound (s : Set ℝ) (n : ℕ)
    (bound : ∀ A : Finset ℝ, (↑A : Set ℝ) ⊆ s → A.card ≤ n) :
    s.Finite :=
  Set.finite_of_forall_finset_card_le s n bound

theorem m50ObservedFiniteness_from_M49
    (V49 : RepairedVolumeLossTheory.{u})
    (g₀ : StandardInitialMetric) (K : MetricSurgeryConstants) :
    ∃ deltaUpper : ℝ, 0 < deltaUpper ∧ deltaUpper ≤ K.delta₀ ∧
      ∀ (B : ℝ) (V₀ : ℝ≥0∞) (hMin : ℝ),
        0 < B → V₀ ≠ (⊤ : ℝ≥0∞) → 0 < hMin →
        ∃ n : ℕ, ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
          F.standard_initial = g₀ → F.local_constants = K → O.H ≤ B →
          RepairedObservedVolumeControls F O →
          calibratedMetricVolume (F.metric 0) Set.univ ≤ V₀ →
          (∀ T ∈ F.surgery_times ∩ surgeryObservationInterval O,
            F.parameters.delta T ≤ deltaUpper ∧ hMin ≤ F.parameters.h T) →
          (F.surgery_times ∩ surgeryObservationInterval O).Finite ∧
            ∀ A : Finset ℝ,
              (↑A : Set ℝ) ⊆ F.surgery_times ∩ surgeryObservationInterval O →
                A.card ≤ n := by
  obtain ⟨deltaUpper, hdelta, hcutoff, _eventLoss, count⟩ := V49.calibrated g₀ K
  refine ⟨deltaUpper, hdelta, hcutoff, ?_⟩
  intro B V₀ hMin hB hV₀ hhMin
  obtain ⟨n, hn⟩ := count B V₀ hMin hB hV₀ hhMin
  refine ⟨n, ?_⟩
  intro F O hg₀ hK hH controls hvolume hscales
  have hcount := hn F O hg₀ hK hH controls hvolume hscales
  exact ⟨finite_of_finset_card_bound _ n hcount, hcount⟩

end PoincareConjecture
