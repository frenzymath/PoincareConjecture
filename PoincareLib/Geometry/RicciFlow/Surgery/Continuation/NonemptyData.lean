import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Branch

/-!
Adapted from Mapher `PoincareMT/Definitions/M41NonemptyContinuation.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# M41 repaired nonempty-terminal continuation data

This branch wrapper selects the nonempty terminal operation from the full
continuation output and keeps the continued carrier and transported surgery
event available to later rows.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

structure RepairedNonemptyContinuationData
    {F : SurgeryFlowData.{u}} {T : ℝ}
    (I : RepairedContinuationInput F T)
    (branch : RepairedBranchContinuationData I) where
  continued_nonempty : Nonempty (branch.conclusion.extension.extended.slice T).carrier
  operation : RepairedNonemptyTerminalOperationCertificate I
    branch.conclusion.extension branch.conclusion.surgery_at_terminal
    continued_nonempty
  operation_eq : branch.conclusion.terminal_operation =
    RepairedTerminalOperation.nonempty continued_nonempty operation
  post_terminal_interval : ∃ d : ℝ, 0 < d ∧
    Set.Ioo T (T + d) ⊆ branch.conclusion.extension.extended.time_domain ∧
    Disjoint branch.conclusion.extension.extended.surgery_times (Set.Ioo T (T + d))
  continued_admissible : SurgeryFlowAdmissible branch.conclusion.extension.extended
  continued_pinched : SurgeryFlowPinched branch.conclusion.extension.extended

end PoincareMT
