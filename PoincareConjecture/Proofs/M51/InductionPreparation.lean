import PoincareConjecture.Proofs.M51.VolumeCalibration
import PoincareConjecture.Proofs.M48.AnalyticCalibration

set_option autoImplicit false

open scoped ENNReal

universe u

namespace PoincareConjecture

theorem m51InductionPreparation
    (S : RepairedControlledSchedulesData.{u}) (P : M48Predecessors.{u})
    (V49 : RepairedVolumeLossTheory.{u})
    (G46 : RepairedNoncollapseInductionTheory.{u})
    (G47 : RepairedCanonicalInductionTheory.{u})
    (E48 : RepairedEpochExtensionTheory.{u}) :
    ∃ d : ℝ, ∃ hd : 0 < d,
      ∃ B : M47ComponentAnalyticBounds.{u} S.setup.C,
        ∃ N : RepairedNoncollapseInductionData
            ((S.calibrateForEpoch B).restrictDelta d hd),
          ∃ C : RepairedCanonicalInductionData
              ((S.calibrateForEpoch B).restrictDelta d hd) N,
            ∃ _E : RepairedEpochExtensionData
                ((S.calibrateForEpoch B).restrictDelta d hd) N C,
              let S' := (S.calibrateForEpoch B).restrictDelta d hd
              d ≤ S'.constants.delta₀ ∧ S'.Delta0 ≤ d ∧
              S'.standard_initial = S.standard_initial ∧
              S'.constants = S.constants ∧ S'.setup.epsilon = S.setup.epsilon ∧
              (∀ (F : SurgeryFlowData.{u}) (V : RepairedVolumeLossControls F),
                F.standard_initial = S'.standard_initial →
                F.local_constants = S'.constants →
                (∀ T ∈ F.surgery_times, F.parameters.delta T ≤ d) →
                Nonempty (RepairedVolumeLossData F V)) ∧
              (∀ (Btime : ℝ) (V₀ : ℝ≥0∞) (hMin : ℝ),
                0 < Btime → V₀ ≠ (⊤ : ℝ≥0∞) → 0 < hMin →
                ∃ n : ℕ, ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
                  F.standard_initial = S'.standard_initial →
                  F.local_constants = S'.constants → O.H ≤ Btime →
                  RepairedObservedVolumeControls F O →
                  calibratedMetricVolume (F.metric 0) Set.univ ≤ V₀ →
                  (∀ T ∈ F.surgery_times ∩ surgeryObservationInterval O,
                    F.parameters.delta T ≤ d ∧ hMin ≤ F.parameters.h T) →
                  ∀ A : Finset ℝ,
                    (↑A : Set ℝ) ⊆ F.surgery_times ∩ surgeryObservationInterval O →
                      A.card ≤ n) := by
  obtain ⟨d, hd, hupper, _hseed, losses, count⟩ := m51VolumeCalibration_from_M49 S V49
  obtain ⟨B, N, C, E⟩ := E48.from_calibrated_predecessors P G46 G47 S d hd
  obtain ⟨E⟩ := E
  exact ⟨d, hd, B, N, C, E, hupper, min_le_right _ _, rfl, rfl, rfl, losses, count⟩

end PoincareConjecture
