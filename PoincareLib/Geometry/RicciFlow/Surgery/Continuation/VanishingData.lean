import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Branch

/-!
Adapted from Mapher `PoincareMT/Definitions/M42VanishingContinuation.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# M42 repaired vanishing-terminal continuation data

This branch wrapper selects the whole-slice-vanishing terminal operation from
the continuation output and records extinction permanence on the extension.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

structure RepairedVanishingContinuationData
    {F : SurgeryFlowData.{u}} {T : ℝ}
    (I : RepairedContinuationInput F T)
    (branch : RepairedBranchContinuationData I) where
  continued_empty : IsEmpty (branch.conclusion.extension.extended.slice T).carrier
  operation : RepairedVanishingTerminalOperationCertificate I
    branch.conclusion.extension branch.conclusion.surgery_at_terminal
    continued_empty
  operation_eq : branch.conclusion.terminal_operation =
    RepairedTerminalOperation.vanishing continued_empty operation
  end_time_top : branch.conclusion.end_time = ⊤
  post_terminal_interval : ∃ d : ℝ, 0 < d ∧
    Set.Ioo T (T + d) ⊆ branch.conclusion.extension.extended.time_domain ∧
    Disjoint branch.conclusion.extension.extended.surgery_times (Set.Ioo T (T + d))
  continued_admissible : SurgeryFlowAdmissible branch.conclusion.extension.extended
  continued_pinched : SurgeryFlowPinched branch.conclusion.extension.extended

end PoincareMT
