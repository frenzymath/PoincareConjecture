import PoincareConjecture.Proofs.M51.GlobalControlledExtension
import PoincareConjecture.Proofs.M51.NormalizedAssembly
import PoincareConjecture.Proofs.M51.GivenPrefixStage










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M51

variable (S : RepairedControlledSchedulesData.{u})
  (N : RepairedNoncollapseInductionData S)
  (C : RepairedCanonicalInductionData S N)
  (A : M48AnalyticCalibration S) (P : M48Predecessors.{u})
  (F50 : RepairedFinitePrefixTheory.{u})
  (d : ℝ) (hd : (M51Numerical.schedule S N C).Delta 0 ≤ d)
  (losses : ∀ (F : SurgeryFlowData.{u}) (V : RepairedVolumeLossControls F),
    F.standard_initial = S.standard_initial → F.local_constants = S.constants →
    (∀ t ∈ F.surgery_times, F.parameters.delta t ≤ d) →
    Nonempty (RepairedVolumeLossData F V))
  (count : ∀ (B : ℝ) (V₀ : ℝ≥0∞) (hMin : ℝ),
    0 < B → V₀ ≠ (⊤ : ℝ≥0∞) → 0 < hMin →
    ∃ bound : ℕ, ∀ (G : SurgeryFlowData.{u}) (O : SurgeryObservation G),
      G.standard_initial = S.standard_initial →
      G.local_constants = S.constants → O.H ≤ B →
      RepairedObservedVolumeControls G O →
      calibratedMetricVolume (G.metric 0) univ ≤ V₀ →
      (∀ t ∈ G.surgery_times ∩ surgeryObservationInterval O,
        G.parameters.delta t ≤ d ∧ hMin ≤ G.parameters.h t) →
      ∀ U : Finset ℝ,
        (↑U : Set ℝ) ⊆ G.surgery_times ∩ surgeryObservationInterval O →
          U.card ≤ bound)

include A P F50 d hd losses count



theorem givenPrefixAssembly
    (delta : ℝ → ℝ)
    (hcut : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
      delta t ≤ (M51Numerical.schedule S N C).Delta j)
    (F : SurgeryFlowData.{u}) (H : ℝ)
    (pref : RepairedGlobalControlledPrefix (M51Numerical.schedule S N C) delta F H) :
    Nonempty (RepairedGlobalControlledExtension (M51Numerical.schedule S N C) F) := by
  rcases controlledPrefix_start P.m13 F50 d hd
      (by simpa only [S.setup_standard_initial_eq] using losses) pref hcut with
      finished | ⟨k, X, _hX, _hH⟩
  · exact finished
  · obtain ⟨Q⟩ := exists_completed_stage_chain_from A P d hd
      (by simpa only [S.setup_standard_initial_eq] using count) delta k X
      pref.delta_eq pref.schedule_agreement hcut
    exact ⟨Q.controlledExtension P.m13 F50 d hd losses delta
      pref.delta_eq pref.schedule_agreement hcut⟩



theorem normalizedFlowAssembly
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [CompactSpace M] [Nonempty M]
    (I : NormalizedInitialMetric (M := M))
    (hRP : NoTrivialNormalProjectivePlane (M := M))
    (delta : ℝ → ℝ) (hmono : AntitoneOn delta (Ici 0))
    (hpos : ∀ t, 0 ≤ t → 0 < delta t)
    (hcut : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
      delta t ≤ (M51Numerical.schedule S N C).Delta j) :
    ∃ G : RepairedGlobalScheduleData I,
      G.flow.local_constants = S.constants ∧
      HEq G.schedule (M51Numerical.schedule S N C) ∧ G.control_function = delta := by
  obtain ⟨F, hstd, hK, hparameters, ⟨e, he⟩, X, _hX⟩ :=
    M51Initial.exists_first_stage S N C I hRP delta hmono hpos hcut
  have hdelta : ∀ t, 0 ≤ t → F.parameters.delta t = delta t := by
    intro t _
    rw [hparameters]
    rfl
  have hprofiles : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
      F.parameters.r t = (M51Numerical.schedule S N C).r j ∧
      F.parameters.kappa t = (M51Numerical.schedule S N C).kappa j ∧
      F.parameters.h t = S.setup.selector.h (delta t * F.parameters.r t) (delta t) := by
    intro j t ht _
    rw [hparameters]
    exact ⟨GlobalSurgerySchedule.parameters_r _ _ _ _ ht,
      GlobalSurgerySchedule.parameters_kappa _ _ _ _ ht, rfl⟩
  obtain ⟨Q⟩ := exists_completed_stage_chain_from A P d hd
    (by simpa only [S.setup_standard_initial_eq] using count) delta 0 X
    hdelta hprofiles hcut
  let R := Q.controlledExtension P.m13 F50 d hd losses delta hdelta hprofiles hcut
  have hepsilon : F.parameters.epsilon = S.setup.epsilon := by rw [hparameters]; rfl
  have hC : F.parameters.C = S.setup.C := by rw [hparameters]; rfl
  obtain ⟨G, _hflow, hconstants, hschedule, hcontrol⟩ :=
    normalizedAssembly S N C P.m13 F50 d hd losses I R hstd hK hepsilon hC
      e he delta hmono hpos hdelta
  exact ⟨G, hconstants, hschedule, hcontrol⟩

end PoincareConjecture.M51
