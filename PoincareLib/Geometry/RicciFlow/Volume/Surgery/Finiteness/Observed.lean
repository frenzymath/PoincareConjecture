import PoincareLib.Geometry.RicciFlow.Surgery.Volume.LossTheory
import PoincareLib.Geometry.RicciFlow.Volume.Surgery.FiniteCardBound

/-!
Adapted from Mapher `PoincareMT/Proofs/M50/ObservedFiniteness.lean` at
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.

# Finiteness from the observed surgery count

This logical consequence applies M49's calibrated raw-flow count. It neither
constructs an extension nor requires equality to a selected M36 operation.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

private theorem finite_of_finset_card_bound (s : Set ℝ) (n : ℕ)
    (bound : ∀ A : Finset ℝ, (↑A : Set ℝ) ⊆ s → A.card ≤ n) :
    s.Finite :=
  Set.finite_of_forall_finset_card_le s n bound

/-- Apply M49's Lemma 17.12 count (Morgan--Tian, pp. 410--411) at its
selected cutoff. The same integer is chosen before every raw flow and
observation, retaining all initial-volume, horizon, height, and observed
geometric guards. An infinite observed surgery set would contain a finite
subset of cardinality `n + 1`, contradicting that count. This is a logical
corollary; continuation and global assembly remain separate obligations. -/
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

end PoincareMT
