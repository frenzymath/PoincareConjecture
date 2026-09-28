import PoincareConjecture.Definitions.M37SurgeryFlow
import PoincareConjecture.Statements.M33BranchContinuation
import PoincareConjecture.Statements.M36MetricSurgery









set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture







def RepairedBranchApplication (B : RepairedBranchContinuationTheory.{u})
    (F : SurgeryFlowData.{u}) : Type (u + 1) :=
    ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T2Space M] [T3Space M] [SecondCountableTopology M],
      ∀ {T : ℝ} (I : RepairedContinuationInput F T),
      ∀ {G : GeneralizedRicciFlowData.{u}},
      ∀ H : SingularTimeAssumptions G T M,
      ∀ L : RepairedSingularRegularLimitData H,
      ∀ N : RepairedHornSelectionData H,
      (bridge : RepairedContinuationLimitBridge H L N I) →
      {certificate : RepairedBranchContinuationData I //
        certificate = Classical.choice
          (B.continuation I H L N bridge)}

structure RepairedSurgeryFlowPackage (g₀ : StandardInitialMetric)
    (S : RepairedMetricSurgeryTheory.{u})
    (B : RepairedBranchContinuationTheory.{u})
    (F : SurgeryFlowData.{u}) where
  data : RepairedSurgeryFlowData.{u} g₀
  compatibility_data : RepairedSurgeryFlowCompatibilityData.{u} g₀
  core_eq : compatibility_data.toRepairedSurgeryFlowData = data
  flow_eq : data.flow = F
  metric_surgery_source :
    compatibility_data.metric_surgery = Classical.choice (S.surgery g₀)
  branch_application : RepairedBranchApplication B F

structure RepairedSurgeryFlowCompatibility
    (S : RepairedMetricSurgeryTheory.{u})
    (B : RepairedBranchContinuationTheory.{u})
    (F : SurgeryFlowData.{u}) where
  data : RepairedSurgeryFlowCompatibilityData.{u} F.standard_initial
  flow_eq : data.flow = F
  metric_surgery_source :
    data.metric_surgery = Classical.choice (S.surgery F.standard_initial)
  branch_application : RepairedBranchApplication B F

structure RepairedSurgeryFlowTheory : Prop where
  flow : ∀ (S : RepairedMetricSurgeryTheory.{u})
    (B : RepairedBranchContinuationTheory.{u}),
    ∀ F : SurgeryFlowData.{u},
    RepairedSurgeryFlowCompatibility S B F →
    Nonempty (RepairedSurgeryFlowPackage.{u} F.standard_initial S B F)

end PoincareConjecture
