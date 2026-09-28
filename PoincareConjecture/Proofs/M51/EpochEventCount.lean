import PoincareConjecture.Proofs.M51.EpochStage
import PoincareConjecture.Proofs.M51.HorizonCount
import PoincareConjecture.Proofs.M48.ExtensionMetric









set_option autoImplicit false

open Set
open scoped ENNReal

universe u

namespace PoincareConjecture.M51

open M51Numerical

namespace EpochStage

variable {S : RepairedControlledSchedulesData.{u}}
  {N : RepairedNoncollapseInductionData S} {C : RepairedCanonicalInductionData S N}
  {n : ℕ} {F : SurgeryFlowData.{u}} (X : EpochStage S N C n F)


theorem initial_volume_eq (H13 : GeneralizedParabolicRescalingTheory.{u} 3) :
    calibratedMetricVolume (X.extension.extended.metric 0) univ =
      calibratedMetricVolume (F.metric 0) univ := by
  simpa only [preimage_univ] using
    ((X.extension.metric_calculus H13 0 F.zero_mem).m48_volume_eq univ).symm



theorem observedVolumeControls (H13 : GeneralizedParabolicRescalingTheory.{u} 3) :
    RepairedObservedVolumeControls X.extension.extended X.observation where
  pinched := fun t ht => X.pinched t (X.observation.interval_subset ht)
  strong_boundaries := fun T hT _ => X.old_controls.admissible.strong_boundaries T hT
  strong_disappearing := fun T hT _ => X.old_controls.admissible.strong_disappearing T hT
  strong_vanishing := fun T hT _ => X.old_controls.admissible.strong_vanishing T hT
  nonempty_pre_interval := X.extension.extended.nonemptyEventPreInterval
  vanishing_pre_interval := X.extension.extended.vanishingEventPreInterval
  zero_cap_discard := X.extension.extended.zeroCapDiscard H13

end EpochStage




theorem uniformEpochEventCount
    (S : RepairedControlledSchedulesData.{u})
    (N : RepairedNoncollapseInductionData S) (C : RepairedCanonicalInductionData S N)
    (n : ℕ) (F : SurgeryFlowData.{u})
    (H13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (d : ℝ) (hd : (schedule S N C).Delta 0 ≤ d)
    (count : ∀ (B : ℝ) (V₀ : ℝ≥0∞) (hMin : ℝ),
      0 < B → V₀ ≠ (⊤ : ℝ≥0∞) → 0 < hMin →
      ∃ bound : ℕ, ∀ (G : SurgeryFlowData.{u}) (O : SurgeryObservation G),
        G.standard_initial = S.setup.standard_initial → G.local_constants = S.constants →
        O.H ≤ B → RepairedObservedVolumeControls G O →
        calibratedMetricVolume (G.metric 0) univ ≤ V₀ →
        (∀ t ∈ G.surgery_times ∩ surgeryObservationInterval O,
          G.parameters.delta t ≤ d ∧ hMin ≤ G.parameters.h t) →
        ∀ A : Finset ℝ,
          (↑A : Set ℝ) ⊆ G.surgery_times ∩ surgeryObservationInterval O → A.card ≤ bound)
    (delta : ℝ → ℝ)
    (hdelta : ∀ t, 0 ≤ t → F.parameters.delta t = delta t)
    (hcut : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
      delta t ≤ (schedule S N C).Delta j) :
    ∃ bound : ℕ, ∀ X : EpochStage S N C n F, ∀ A : Finset ℝ,
      (↑A : Set ℝ) ⊆ X.extension.extended.surgery_times ∩
        surgeryObservationInterval X.observation → A.card ≤ bound := by
  let B := surgeryEpochStart ((prefixAt S N C n).i + 1)
  have hB : 0 < B := by dsimp [B, surgeryEpochStart]; positivity
  obtain ⟨bound, hbound⟩ := count B (calibratedMetricVolume (F.metric 0) univ)
    (F.parameters.h B) hB (initialVolume_ne_top F) (F.parameters.h_pos B hB.le)
  refine ⟨bound, ?_⟩
  intro X
  apply hbound X.extension.extended X.observation
    (by simpa only [prefix_setup] using X.old_controls.standard_initial_eq)
    X.old_controls.local_constants_eq X.horizon_le (X.observedVolumeControls H13)
    (X.initial_volume_eq H13).le
  intro t ht
  have ht0 : 0 ≤ t := ht.2.1
  obtain ⟨j, hj⟩ := exists_surgeryEpochEntry ht0
  refine ⟨?_, ?_⟩
  · rw [X.delta_eq hdelta t ht0]
    exact (hcut j t hj ht0).trans (((schedule S N C).Delta_antitone (Nat.zero_le j)).trans hd)
  · have hlow := X.extension.extended.parameters.h_antitone ht0 hB.le
      (ht.2.2.le.trans X.horizon_le)
    simpa only [X.extension.parameters_eq] using hlow

end PoincareConjecture.M51
