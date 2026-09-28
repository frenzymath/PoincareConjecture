import PoincareConjecture.Proofs.M72.Providers
import PoincareConjecture.Proofs.M52.ComparisonCalibration









set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture














theorem m72CalibratedGlobalFlowWithRawTopology
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
    ∃ K : MetricSurgeryConstants, ∃ S : GlobalSurgerySchedule K,
      ∀ {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
        [SecondCountableTopology M] [CompactSpace M] [Nonempty M],
        ∀ (N : NormalizedInitialMetric (M := M)),
          NoTrivialNormalProjectivePlane (M := M) →
          ∃ G : RepairedGlobalFlowData N,
            G.schedule.flow.local_constants = K ∧
            HEq G.schedule.schedule S ∧
            G.schedule.control_function = m52ComparisonControl S ∧
            Nonempty (RawLocalSurgeryTopologyData G.certificate.flow) ∧
            (∀ t : ℝ, 0 ≤ t →
              G.certificate.flow.parameters.delta t < S.Delta 0 ∧
              G.certificate.flow.parameters.delta t ≤
                G.certificate.flow.local_constants.delta₀ / 2 ∧
              G.certificate.flow.parameters.h t ≤
                G.certificate.flow.local_constants.R₀ ^ (-1 / 2 : ℝ) / 2 ∧
              G.certificate.flow.parameters.delta t < G.certificate.flow.local_constants.delta₀ ∧
              G.certificate.flow.parameters.h t <
                G.certificate.flow.local_constants.R₀ ^ (-1 / 2 : ℝ)) := by
  obtain ⟨K, S, start⟩ := m72GlobalFlowWithRawTopology A B28 E34 U35 S36 P44 L15 U43
    S45 N46 C47 E48 P48 V49 F50 G51
  refine ⟨K, S, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ _ N hprojective
  obtain ⟨G, hK, hS, hdelta, htopology⟩ :=
    start N hprojective (m52ComparisonControl S)
      ((m52ComparisonControl_antitone S).antitoneOn _)
      (fun t _ => m52ComparisonControl_pos S t)
      (fun j _ ht _ => m52ComparisonControl_le_epoch S j ht)
  exact ⟨G, hK, hS, hdelta, htopology, m52StrictComparisonBounds G S hK hdelta⟩

end PoincareConjecture
