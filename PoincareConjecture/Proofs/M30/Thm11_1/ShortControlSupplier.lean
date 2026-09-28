import PoincareConjecture.Proofs.M30.Thm11_1.StaticTerminalBound
import PoincareConjecture.Proofs.M30.Thm11_1.TerminalStaticLimit
import PoincareConjecture.Proofs.M30.Thm11_1.ShortLimitStatementAssembly
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.AnalyticSuppliers










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold




theorem shortControlService (hC : RicciFlowCurvatureTheory.{u}) :
    M30ShortControlService.{u} := by
  classical
  obtain ⟨epsilon0, hpositive, _hsmall, hterminalBound⟩ :=
    exists_static_limit_terminal_curvature_bound_threshold.{u}
  refine ⟨epsilon0, hpositive, ?_⟩
  intro S epsilon C kappa r0 mu hepsilon H hbound
  obtain ⟨G, hcomplete, hcoverage⟩ :=
    exists_complete_terminal_static_limit hC H hbound
  let D : LeviCivitaData G.limitMetric := G.limitMetric.leviCivitaData
  obtain ⟨B, _hB, hscalar, _hcurvature⟩ :=
    hterminalBound hC H hepsilon hbound G hcomplete D
  exact ⟨G.subsequence, G.subsequence_strictMono,
    shortControls_of_static_terminal_limit_bound hC H G D hcoverage (B := B) hscalar⟩



theorem exists_shortLimitStatement
    (P : M30ControlledBlowupPredecessors.{u}) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 400 ∧
      M30ShortLimitStatement.{u} epsilon0 :=
  exists_shortLimitStatement_of_controlService P
    withinFlowJetBoundsService.{0, 0} withinBilinearFlowService.{0}
    spatialSliceJetConvergenceService.{0, 0, 0, 0, 0} (shortControlService P.m04)

end PoincareConjecture.M30
