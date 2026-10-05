import PoincareLib.Geometry.RicciFlow.Blowup.Construction.ShortTime.StaticLimit.StaticTerminalBound
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.ShortTime.Terminal.TerminalStaticLimit
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.ShortTime.ShortLimitStatementAssembly
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.PartialLimits.AnalyticSuppliers

/-!
# Actual short controls and the short limit statement

Morgan--Tian Theorem 11.1, pp. 267-271. The bounded complete terminal
limit and its retained all-radius source coverage produce one common
short lifetime on the selected sequence. The checked finite convergence
assembly then gives the frozen short conclusion for the original sequence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

/-- The actual bounded terminal limit supplies short controls on its
retained subsequence below a universal accuracy threshold
(Theorem 11.1 after Claim 11.7, p. 271). -/
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

/-- The actual short-control and included-time analytic suppliers give
the frozen short-limit statement (Theorem 11.1, pp. 267-271). -/
theorem exists_shortLimitStatement
    (P : M30ControlledBlowupPredecessors.{u}) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 400 ∧
      M30ShortLimitStatement.{u} epsilon0 :=
  exists_shortLimitStatement_of_controlService P
    withinFlowJetBoundsService.{0, 0} withinBilinearFlowService.{0}
    spatialSliceJetConvergenceService.{0, 0, 0, 0, 0} (shortControlService P.m04)

end PoincareMT.M30
