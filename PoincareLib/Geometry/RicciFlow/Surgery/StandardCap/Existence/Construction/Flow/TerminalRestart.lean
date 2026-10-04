import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Construction.Flow.TerminalCutoffFlows
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Construction.Basic.Restart.Existence

/-!
# Forward Ricci flow from the complete terminal metric

The actual cutoff doubles and their common-time flows supply the
metric-general extraction. The resulting complete forward flow starts
at the terminal metric with any supplied compatible connection and a
global curvature bound. Joining to the old flow is a separate step in
Morgan-Tian Theorem 12.5, pp. 296-297.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareMT.M34.PartialFlowTerminalJets

variable {g0 : StandardInitialMetric} {F : PartialStandardCapFlow g0} {S : ℝ}
  (L : PartialFlowTerminalJets F S) (P : M34StandardCapPredecessors)
  (E0 : StandardCapEstimate g0) {B : ℝ} (hS : 0 < S) (hSF : S ≤ F.lifetime) (hB : 0 < B)
  (hfull : ∀ t ∈ Ico 0 S, ∀ x : StandardCapSpace,
    (F.flow.connection t).curvatureTensorNorm x ≤ B)

/-- A bounded past admits an actual complete forward Ricci flow from
its terminal metric, retaining a prescribed compatible connection
(Theorem 12.5, pp. 296-297). -/
theorem forward_flow_exists
    (D : LeviCivitaData (L.metric P.curvature E0 hS hSF hB hfull)) :
    ∃ τ K : ℝ, 0 < τ ∧ 0 < K ∧
      ∃ H : RicciFlow 3 StandardCapSpace (Ico 0 τ),
        H.metric 0 = L.metric P.curvature E0 hS hSF hB hfull ∧
          HEq (H.connection 0) D ∧
          (∀ t ∈ Ico 0 τ, MetricComplete (H.metric t)) ∧
          ∀ t ∈ Ico 0 τ, ∀ x : StandardCapSpace,
            |(H.connection t).curvatureTensorNorm x| ≤ K := by
  obtain ⟨A⟩ := L.metricFlowApproximation_exists P E0 hS hSF hB hfull
  obtain ⟨H, hinit, hD, hcomplete, hcurv⟩ := A.complete_flow_exists D P.curvature
    (L.metric_complete P.curvature E0 hS hSF hB hfull)
  exact ⟨A.time, A.curvature_bound 0, A.time_pos, A.bound_pos 0,
    H, hinit, hD, hcomplete, hcurv⟩

end PoincareMT.M34.PartialFlowTerminalJets
