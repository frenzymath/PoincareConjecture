import PoincareConjecture.Proofs.M38
import PoincareConjecture.Proofs.M52
import PoincareConjecture.Proofs.M72.LocalTopology










set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

theorem m72GlobalEpsilonBound
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M]
    {N : NormalizedInitialMetric (M := M)}
    (G : RepairedGlobalFlowData N) {K : MetricSurgeryConstants}
    (schedule : GlobalSurgerySchedule K)
    (hK : G.schedule.flow.local_constants = K)
    (hschedule : HEq G.schedule.schedule schedule)
    {bound : ℝ} (hbound : 2 * schedule.setup.epsilon ≤ bound) :
    2 * G.certificate.flow.parameters.epsilon ≤ bound := by
  rw [G.flow_eq, G.schedule.parameters_epsilon_eq]
  cases hK
  have hs : G.schedule.schedule = schedule := eq_of_heq hschedule
  rw [hs]
  exact hbound














theorem m72GlobalFlowWithRawTopology
    (A : RepairedNeckCapTopologyTheory.{u})
    (B28 : RepairedBoundedDistanceTheory.{u})
    (E34 : RepairedStandardCapExistenceTheory)
    (U35 : RepairedStandardCapUniquenessTheory)
    (S36 : RepairedMetricSurgeryTheory.{u})
    (P44 : RepairedCapPersistenceTheory.{u})
    (L15 : GeneralizedNoncollapsingConclusion.{u} 3)
    (U43 : RepairedUnifiedContinuationTheory.{u})
    (S45 : RepairedControlledSchedulesTheory.{u})
    (N46 : RepairedNoncollapseInductionTheory.{u})
    (C47 : RepairedCanonicalInductionTheory.{u})
    (E48 : RepairedEpochExtensionTheory.{u})
    (P48 : M48Predecessors.{u})
    (V49 : RepairedVolumeLossTheory.{u})
    (F50 : RepairedFinitePrefixTheory.{u})
    (G51 : RepairedGlobalScheduleTheory.{u}) :
    ∃ K : MetricSurgeryConstants, ∃ schedule : GlobalSurgerySchedule K,
      ∀ {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
        [SecondCountableTopology M] [CompactSpace M] [Nonempty M],
        ∀ (N : NormalizedInitialMetric (M := M)),
          NoTrivialNormalProjectivePlane (M := M) →
          ∀ delta : ℝ → ℝ,
            AntitoneOn delta (Set.Ici 0) →
            (∀ t, 0 ≤ t → 0 < delta t) →
            (∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t → delta t ≤ schedule.Delta j) →
            ∃ G : RepairedGlobalFlowData N,
              G.schedule.flow.local_constants = K ∧
              HEq G.schedule.schedule schedule ∧
              G.schedule.control_function = delta ∧
              Nonempty (RawLocalSurgeryTopologyData G.certificate.flow) := by
  obtain ⟨epsilon, hepsilon, _hneck, htopology⟩ := rawLocalSurgeryTopology.topology A
  obtain ⟨K, schedule, hbound, _extend, start⟩ :=
    repairedGlobalFlow.global_flow B28 E34 U35 S36 P44 L15 U43 S45 N46 C47 E48 P48 V49
      F50 G51 epsilon hepsilon
  refine ⟨K, schedule, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ _ N hprojective delta hantitone hpositive hcutoff
  obtain ⟨G, hK, hschedule, hdelta⟩ :=
    start N hprojective delta hantitone hpositive hcutoff
  exact ⟨G, hK, hschedule, hdelta,
    htopology G.certificate.flow G.certificate.admissible
      (m72GlobalEpsilonBound G schedule hK hschedule hbound)⟩




noncomputable def m72ReconstructionInputFromRaw
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M]
    {N : NormalizedInitialMetric (M := M)}
    (G : RepairedGlobalFlowData N)
    (L : RawLocalSurgeryTopologyData G.certificate.flow)
    (E : FiniteExtinctionConclusion G.certificate.flow)
    (hconnected : IsConnected (Set.univ : Set M)) : M72ReconstructionInput N where
  global := G
  extinction := E
  initial_connected := hconnected
  local_topology := m72LocalTopologyFromRaw G.certificate L E.extinction_time

end PoincareConjecture
