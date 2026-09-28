import PoincareConjecture.Statements.M52GlobalFlow
import PoincareConjecture.Statements.M57Transport
import PoincareConjecture.Definitions.M67
import PoincareConjecture.Proofs.M52.Assembly
import PoincareConjecture.Proofs.M52.ComparisonCalibration















set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture



theorem m71GlobalEpsilonBound
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M]
    {N : NormalizedInitialMetric (M := M)}
    (G : RepairedGlobalFlowData N) {K0 : MetricSurgeryConstants}
    (S : GlobalSurgerySchedule K0)
    (hK0 : G.schedule.flow.local_constants = K0)
    (hS : HEq G.schedule.schedule S)
    {bound : ℝ} (hbound : 2 * S.setup.epsilon ≤ bound) :
    2 * G.certificate.flow.parameters.epsilon ≤ bound := by
  rw [G.flow_eq, G.schedule.parameters_epsilon_eq]
  cases hK0
  have hs : G.schedule.schedule = S := eq_of_heq hS
  rw [hs]
  exact hbound




















theorem m71GlobalFlowWithComparisons
    (A25 : RepairedNeckCapTopologyTheory.{u})
    (G38 : RawLocalSurgeryTopologyTheory.{u})
    (G39 : RepairedComparisonMapTheory.{u})
    (G40 : RepairedComparisonHomotopyTheory.{u})
    (P02 : RepairedClosedTopologyProvider.{u})
    (G52 : RepairedGlobalFlowTheory.{u})
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
    ∃ K0 : MetricSurgeryConstants, ∃ S : GlobalSurgerySchedule K0,
      ∀ {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
        [SecondCountableTopology M] [CompactSpace M] [Nonempty M],
        ∀ (N : NormalizedInitialMetric (M := M)),
          NoTrivialNormalProjectivePlane (M := M) →
          ∃ G : RepairedGlobalFlowData N,
          ∃ _L : RawLocalSurgeryTopologyData G.certificate.flow,
          ∃ K : RepairedComparisonMapData (m52CoreFlowData G),
          ∃ C : RepairedComparisonHomotopyData (m52CoreFlowData G) K,
            G.schedule.flow.local_constants = K0 ∧
            HEq G.schedule.schedule S ∧
            G.schedule.control_function = m52ComparisonControl S ∧
            RepairedComparisonMapProviderRealization G39 (m52CoreFlowData G) K ∧
            RepairedComparisonProviderRealization G40 (m52CoreFlowData G) C ∧
            M67EventComparisonBounds G.certificate.flow Set.univ ∧
            (∀ t : ℝ, 0 ≤ t →
              G.certificate.flow.parameters.delta t < S.Delta 0 ∧
              G.certificate.flow.parameters.delta t ≤
                G.certificate.flow.local_constants.delta₀ / 2 ∧
              G.certificate.flow.parameters.h t ≤
                G.certificate.flow.local_constants.R₀ ^ (-1 / 2 : ℝ) / 2 ∧
              G.certificate.flow.parameters.delta t <
                G.certificate.flow.local_constants.delta₀ ∧
              G.certificate.flow.parameters.h t <
                G.certificate.flow.local_constants.R₀ ^ (-1 / 2 : ℝ)) := by
  classical
  let e38 := Classical.choose (G38.topology A25)
  have h38 := Classical.choose_spec (G38.topology A25)
  let e39 := Classical.choose G39.comparison
  have h39 := Classical.choose_spec G39.comparison
  let e40 := Classical.choose (G40.homotopy P02 G39)
  have h40 := Classical.choose_spec (G40.homotopy P02 G39)
  have hpositive : 0 < min e38 (min e39 e40) :=
    lt_min h38.1 (lt_min h39.1 h40.1)
  obtain ⟨K0, S, hbound, _extend, start⟩ :=
    G52.global_flow B28 E34 U35 S36 P44 L15 U43 S45 N46 C47 E48 P48 V49 F50 G51
      (min e38 (min e39 e40)) hpositive
  refine ⟨K0, S, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ _ N hprojective
  obtain ⟨G, hK0, hS, hdelta⟩ :=
    start N hprojective (m52ComparisonControl S)
      ((m52ComparisonControl_antitone S).antitoneOn _)
      (fun t _ => m52ComparisonControl_pos S t)
      (fun j _ ht _ => m52ComparisonControl_le_epoch S j ht)
  have hsmall := m71GlobalEpsilonBound G S hK0 hS hbound
  have hsmall38 : 2 * G.certificate.flow.parameters.epsilon ≤ e38 :=
    hsmall.trans (min_le_left _ _)
  have hsmall39 : 2 * (m52CoreFlowData G).flow.parameters.epsilon ≤ e39 :=
    hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsmall40 : 2 * (m52CoreFlowData G).flow.parameters.epsilon ≤ e40 :=
    hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  let L := Classical.choice
    (h38.2.2 G.certificate.flow G.certificate.admissible hsmall38)
  let K := Classical.choice (h39.2 (m52CoreFlowData G) hsmall39)
  have hK : RepairedComparisonMapProviderRealization G39 (m52CoreFlowData G) K :=
    ⟨hsmall39, rfl⟩
  let C := Classical.choice (h40.2 (m52CoreFlowData G) hsmall40 K hK)
  have hC : RepairedComparisonProviderRealization G40 (m52CoreFlowData G) C :=
    ⟨P02, G39, hsmall40, hK, rfl⟩
  have hbounds := m52StrictComparisonBounds G S hK0 hdelta
  have hcomparison : M67EventComparisonBounds G.certificate.flow Set.univ := by
    intro t _ ht
    have ht0 := G.certificate.flow.time_domain_nonnegative
      (G.certificate.flow.surgery_times_subset ht)
    exact ⟨(hbounds t ht0).2.2.2.1, (hbounds t ht0).2.2.2.2⟩
  exact ⟨G, L, K, C, hK0, hS, hdelta, hK, hC, hcomparison, hbounds⟩

end PoincareConjecture
