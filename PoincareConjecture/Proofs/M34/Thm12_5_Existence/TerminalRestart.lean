import PoincareConjecture.Proofs.M34.Thm12_5_Existence.TerminalCutoffFlows
import PoincareConjecture.Proofs.M34.Thm12_5_Existence.Restart.Existence

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34.PartialFlowTerminalJets

variable {g0 : StandardInitialMetric} {F : PartialStandardCapFlow g0} {S : ℝ}
  (L : PartialFlowTerminalJets F S) (P : M34StandardCapPredecessors)
  (E0 : StandardCapEstimate g0) {B : ℝ} (hS : 0 < S) (hSF : S ≤ F.lifetime) (hB : 0 < B)
  (hfull : ∀ t ∈ Ico 0 S, ∀ x : StandardCapSpace,
    (F.flow.connection t).curvatureTensorNorm x ≤ B)

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

end PoincareConjecture.M34.PartialFlowTerminalJets
