import PoincareConjecture.Definitions.M33BranchContinuation








set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

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

end PoincareConjecture
