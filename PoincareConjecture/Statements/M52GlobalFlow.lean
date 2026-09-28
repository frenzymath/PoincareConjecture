import PoincareConjecture.Definitions.M52GlobalFlow
import PoincareConjecture.Statements.M43UnifiedContinuation
import PoincareConjecture.Statements.M51GlobalSchedule










set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture







































structure RepairedGlobalFlowTheory : Prop where
  global_flow :
    RepairedBoundedDistanceTheory.{u} →
    RepairedStandardCapExistenceTheory →
    RepairedStandardCapUniquenessTheory →
    RepairedMetricSurgeryTheory.{u} →
    RepairedCapPersistenceTheory.{u} →
    GeneralizedNoncollapsingConclusion.{u} 3 →
    RepairedUnifiedContinuationTheory.{u} →
    RepairedControlledSchedulesTheory.{u} →
    RepairedNoncollapseInductionTheory.{u} →
    RepairedCanonicalInductionTheory.{u} →
    RepairedEpochExtensionTheory.{u} →
    M48Predecessors.{u} →
    RepairedVolumeLossTheory.{u} →
    RepairedFinitePrefixTheory.{u} →
    RepairedGlobalScheduleTheory.{u} →
      ∀ epsilon_bound : ℝ, 0 < epsilon_bound →
      ∃ K : MetricSurgeryConstants,
        ∃ schedule : GlobalSurgerySchedule K,
          2 * schedule.setup.epsilon ≤ epsilon_bound ∧
          (∀ (delta : ℝ → ℝ),
            AntitoneOn delta (Set.Ici 0) →
            (∀ t, 0 ≤ t → 0 < delta t) →
            (∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
              delta t ≤ schedule.Delta j) →
            ∀ (F : SurgeryFlowData.{u}) (T : ℝ),
              RepairedGlobalControlledPrefix schedule delta F T →
                Nonempty (RepairedGlobalControlledExtension schedule F)) ∧
          (∀ {M : Type u} [TopologicalSpace M] [MeasurableSpace M]
            [BorelSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
            [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
            [SecondCountableTopology M] [CompactSpace M] [Nonempty M],
            ∀ (N : NormalizedInitialMetric (M := M)),
              NoTrivialNormalProjectivePlane (M := M) →
              ∀ (delta : ℝ → ℝ),
                AntitoneOn delta (Set.Ici 0) →
                (∀ t, 0 ≤ t → 0 < delta t) →
                (∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
                  delta t ≤ schedule.Delta j) →
                ∃ G : RepairedGlobalFlowData N,
                  G.schedule.flow.local_constants = K ∧
                  HEq G.schedule.schedule schedule ∧
                  G.schedule.control_function = delta)

end PoincareConjecture
