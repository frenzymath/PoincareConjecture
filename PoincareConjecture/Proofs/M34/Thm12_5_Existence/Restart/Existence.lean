import PoincareConjecture.Proofs.M34.Thm12_5_Existence.Restart.Curvature
import PoincareConjecture.Proofs.M34.Thm12_5_Existence.Restart.Completeness











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34.MetricFlowApproximation

variable {ginit : RiemannianMetric 3 StandardCapSpace} {Mfamily : ℕ → Type}
  [∀ k, TopologicalSpace (Mfamily k)] [∀ k, ChartedSpace StandardCapSpace (Mfamily k)]
  [∀ k, IsManifold (𝓡 3) ∞ (Mfamily k)] (A : MetricFlowApproximation ginit Mfamily)




theorem complete_flow_exists (Dinit : LeviCivitaData ginit)
    (P : RicciFlowCurvatureTheory.{0}) (hcomplete : MetricComplete ginit) :
    ∃ H : RicciFlow 3 StandardCapSpace (Ico 0 A.time),
      H.metric 0 = ginit ∧ HEq (H.connection 0) Dinit ∧
        (∀ t ∈ Ico 0 A.time, MetricComplete (H.metric t)) ∧
        ∀ t ∈ Ico 0 A.time, ∀ x : StandardCapSpace,
          |(H.connection t).curvatureTensorNorm x| ≤ A.curvature_bound 0 := by
  obtain ⟨G⟩ := metricInteriorCoefficientLimit_exists A P
  refine ⟨G.initialFlow Dinit P, G.initialFlow_metric_zero Dinit P,
    G.initialFlow_connection_zero Dinit P, ?_, ?_⟩
  · exact fun _ ht => G.initialFlow_complete Dinit P hcomplete ht
  · exact fun _ ht x => G.initialFlow_abs_curvature_le Dinit P ht x

end PoincareConjecture.M34.MetricFlowApproximation
