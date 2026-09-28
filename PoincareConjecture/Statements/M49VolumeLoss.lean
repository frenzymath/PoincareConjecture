import PoincareConjecture.Definitions.M49VolumeLoss





































set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure RepairedVolumeLossTheory : Prop where


  calibrated : ∀ (g₀ : StandardInitialMetric) (K : MetricSurgeryConstants),
    ∃ deltaUpper : ℝ, 0 < deltaUpper ∧ deltaUpper ≤ K.delta₀ ∧
      (∀ F : SurgeryFlowData.{u},
        ∀ C : RepairedVolumeLossControls F,
          F.standard_initial = g₀ → F.local_constants = K →
          (∀ T ∈ F.surgery_times, F.parameters.delta T ≤ deltaUpper) →
          Nonempty (RepairedVolumeLossData F C)) ∧
      (∀ (B : ℝ) (V₀ : ℝ≥0∞) (hMin : ℝ),
        0 < B → V₀ ≠ (⊤ : ℝ≥0∞) → 0 < hMin →
        ∃ n : ℕ, ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
          F.standard_initial = g₀ → F.local_constants = K → O.H ≤ B →
          RepairedObservedVolumeControls F O →
          calibratedMetricVolume (F.metric 0) Set.univ ≤ V₀ →
          (∀ T ∈ F.surgery_times ∩ surgeryObservationInterval O,
            F.parameters.delta T ≤ deltaUpper ∧ hMin ≤ F.parameters.h T) →
          ∀ S : Finset ℝ,
            (↑S : Set ℝ) ⊆ F.surgery_times ∩ surgeryObservationInterval O →
              S.card ≤ n)

end PoincareConjecture
