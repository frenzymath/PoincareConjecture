import PoincareConjecture.Proofs.M51.PrefixVolumeControls
import PoincareConjecture.Proofs.M45.InitialGeometry
import PoincareConjecture.Statements.M50FinitePrefix

set_option autoImplicit false

open scoped ENNReal

universe u

namespace PoincareConjecture.M51

theorem initialVolume_ne_top (F : SurgeryFlowData.{u}) :
    calibratedMetricVolume (F.metric 0) Set.univ ≠ ⊤ :=
  F.normalizedInitialData.volume_finite.ne

private theorem finite_of_card_bound (s : Set ℝ) (n : ℕ)
    (h : ∀ A : Finset ℝ, (↑A : Set ℝ) ⊆ s → A.card ≤ n) : s.Finite := by
  classical
  by_contra hinfinite
  obtain ⟨A, hA, hcard⟩ := Set.Infinite.exists_subset_card_eq hinfinite (n + 1)
  have hle : n + 1 ≤ n := by simpa only [hcard] using h A hA
  exact Nat.not_succ_le_self n hle

theorem uniformPrefixEventCount
    {K : MetricSurgeryConstants} (S : GlobalSurgerySchedule K)
    (H13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (d : ℝ) (hd : S.Delta 0 ≤ d)
    (count : ∀ (B : ℝ) (V₀ : ℝ≥0∞) (hMin : ℝ),
      0 < B → V₀ ≠ (⊤ : ℝ≥0∞) → 0 < hMin →
      ∃ n : ℕ, ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
        F.standard_initial = S.setup.standard_initial → F.local_constants = K →
        O.H ≤ B → RepairedObservedVolumeControls F O →
        calibratedMetricVolume (F.metric 0) Set.univ ≤ V₀ →
        (∀ t ∈ F.surgery_times ∩ surgeryObservationInterval O,
          F.parameters.delta t ≤ d ∧ hMin ≤ F.parameters.h t) →
        ∀ A : Finset ℝ,
          (↑A : Set ℝ) ⊆ F.surgery_times ∩ surgeryObservationInterval O → A.card ≤ n)
    (delta : ℝ → ℝ) (hpos : ∀ t, 0 ≤ t → 0 < delta t)
    (hdelta : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t → delta t ≤ S.Delta j)
    (B : ℝ) (V₀ : ℝ≥0∞) (hB : 0 < B) (hV₀ : V₀ ≠ ⊤) :
    ∃ n : ℕ, ∀ (F : SurgeryFlowData.{u}) (H : ℝ),
      RepairedGlobalControlledPrefix S delta F H → H ≤ B →
      calibratedMetricVolume (F.metric 0) Set.univ ≤ V₀ →
      F.surgery_times.Finite ∧
        ∀ A : Finset ℝ, (↑A : Set ℝ) ⊆ F.surgery_times → A.card ≤ n := by
  obtain ⟨k, hk⟩ := exists_surgeryEpochEntry hB.le
  let hMin := S.setup.selector.h (delta B * S.r k) (delta B)
  have hhMin : 0 < hMin :=
    S.setup.selector.h_pos _ _ (mul_pos (hpos B hB.le) (S.r_pos k)) (hpos B hB.le)
  obtain ⟨n, hn⟩ := count B V₀ hMin hB hV₀ hhMin
  refine ⟨n, ?_⟩
  intro F H P hHB hvolume
  have hevents : F.surgery_times ∩ surgeryObservationInterval P.observation =
      F.surgery_times := by
    apply Set.inter_eq_left.mpr
    intro t ht
    change t ∈ Set.Ico 0 H
    rw [← P.time_domain_eq]
    exact F.surgery_times_subset ht
  have hscales : ∀ t ∈ F.surgery_times ∩ surgeryObservationInterval P.observation,
      F.parameters.delta t ≤ d ∧ hMin ≤ F.parameters.h t := by
    intro t ht
    have htime : t ∈ Set.Ico 0 H := ht.2
    exact ⟨P.event_delta_le d hd hdelta ht.1,
      P.height_lower_bound hB.le hk htime.1 (htime.2.le.trans hHB)⟩
  have hcount := hn F P.observation P.standard_initial_eq P.local_constants_eq
    hHB (P.observedVolumeControls H13) hvolume hscales
  rw [hevents] at hcount
  exact ⟨finite_of_card_bound _ n hcount, hcount⟩

theorem selectedPrefixLoss
    {K : MetricSurgeryConstants} (S : GlobalSurgerySchedule K)
    (H13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (V50 : RepairedFinitePrefixTheory.{u})
    (d : ℝ) (hd : S.Delta 0 ≤ d)
    (losses : ∀ (F : SurgeryFlowData.{u}) (C : RepairedVolumeLossControls F),
      F.standard_initial = S.setup.standard_initial → F.local_constants = K →
      (∀ t ∈ F.surgery_times, F.parameters.delta t ≤ d) →
      Nonempty (RepairedVolumeLossData F C))
    {delta : ℝ → ℝ}
    (hdelta : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t → delta t ≤ S.Delta j)
    {F : SurgeryFlowData.{u}} {H : ℝ}
    (P : RepairedGlobalControlledPrefix S delta F H) :
    ∃ V : RepairedVolumeLossData F (P.volumeControls H13),
      Nonempty (RepairedFinitePrefixData F (P.volumeControls H13) V) ∧
        F.surgery_times.Finite := by
  obtain ⟨V⟩ := losses F (P.volumeControls H13) P.standard_initial_eq
    P.local_constants_eq (fun _ ht => P.event_delta_le d hd hdelta ht)
  obtain ⟨Q⟩ := V50.finite_prefix F (P.volumeControls H13) V
  refine ⟨V, ⟨Q⟩, (Q.local_finite (Set.Icc 0 H) isCompact_Icc).subset ?_⟩
  intro t ht
  have htime : t ∈ Set.Ico 0 H := P.time_domain_eq ▸ F.surgery_times_subset ht
  exact ⟨ht, htime.1, htime.2.le⟩

end PoincareConjecture.M51
