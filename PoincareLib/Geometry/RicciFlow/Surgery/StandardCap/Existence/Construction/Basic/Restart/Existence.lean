import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Construction.Curvature.Restart.Curvature
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Construction.Basic.Restart.Completeness

/-!
# Complete flow existence from actual fixed-coordinate approximations

The metric-general extraction produces a complete Ricci flow with a
global full-curvature bound and the exact supplied initial metric and
connection records. The only geometric hypotheses are the approximation
data and initial completeness. This is the restart construction for
Morgan-Tian Theorem 12.5, pp. 296-297.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareMT.M34.MetricFlowApproximation

variable {ginit : RiemannianMetric 3 StandardCapSpace} {Mfamily : ℕ → Type}
  [∀ k, TopologicalSpace (Mfamily k)] [∀ k, ChartedSpace StandardCapSpace (Mfamily k)]
  [∀ k, IsManifold (𝓡 3) ∞ (Mfamily k)] (A : MetricFlowApproximation ginit Mfamily)

/-- Actual approximation data give a complete initial-slab flow that
retains both supplied records and the same uniform full-curvature bound
(Theorem 12.5, pp. 296-297). -/
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

end PoincareMT.M34.MetricFlowApproximation
