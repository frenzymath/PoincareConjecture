import PoincareConjecture.Definitions.M45InitialPrefix
import PoincareConjecture.Statements.M49VolumeLoss

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

theorem m51VolumeCalibration_from_M49
    (B : RepairedControlledSchedulesData.{u}) (V49 : RepairedVolumeLossTheory.{u}) :
    ∃ deltaUpper : ℝ, ∃ hpos : 0 < deltaUpper,
      deltaUpper ≤ B.constants.delta₀ ∧
      (B.restrictDelta deltaUpper hpos).Delta0 ≤ deltaUpper ∧
      (∀ (F : SurgeryFlowData.{u}) (C : RepairedVolumeLossControls F),
        F.standard_initial = (B.restrictDelta deltaUpper hpos).standard_initial →
        F.local_constants = (B.restrictDelta deltaUpper hpos).constants →
        (∀ T ∈ F.surgery_times, F.parameters.delta T ≤ deltaUpper) →
        Nonempty (RepairedVolumeLossData F C)) ∧
      (∀ (Btime : ℝ) (V₀ : ℝ≥0∞) (hMin : ℝ),
        0 < Btime → V₀ ≠ (⊤ : ℝ≥0∞) → 0 < hMin →
        ∃ n : ℕ, ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
          F.standard_initial = B.standard_initial →
          F.local_constants = B.constants →
          O.H ≤ Btime →
          RepairedObservedVolumeControls F O →
          calibratedMetricVolume (F.metric 0) Set.univ ≤ V₀ →
          (∀ T ∈ F.surgery_times ∩ surgeryObservationInterval O,
            F.parameters.delta T ≤ deltaUpper ∧ hMin ≤ F.parameters.h T) →
          ∀ S : Finset ℝ,
            (↑S : Set ℝ) ⊆ F.surgery_times ∩ surgeryObservationInterval O →
              S.card ≤ n) := by
  obtain ⟨deltaUpper, hpos, hle, losses, count⟩ :=
    V49.calibrated B.standard_initial B.constants
  refine ⟨deltaUpper, hpos, hle, min_le_right _ _, ?_, ?_⟩
  · intro F C hg₀ hK hdelta
    exact losses F C hg₀ hK hdelta
  · intro Btime V₀ hMin hBtime hV₀ hhMin
    obtain ⟨n, hn⟩ := count Btime V₀ hMin hBtime hV₀ hhMin
    refine ⟨n, ?_⟩
    intro F' O hg₀' hK' hH controls hvolume hscales
    exact hn F' O hg₀' hK' hH controls hvolume hscales

end PoincareConjecture
