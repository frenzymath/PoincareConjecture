import PoincareConjecture.Statements.M48EpochExtension
import PoincareConjecture.Proofs.M48.PrefixControls
import PoincareConjecture.Proofs.M48.RicciNormTransport
import PoincareConjecture.Proofs.M48.ScalarEvolution
import PoincareConjecture.Proofs.M48.LimitCalibration
import PoincareConjecture.Proofs.M48.AnalyticCalibration
import PoincareConjecture.Proofs.M48.RegularHistory
import PoincareConjecture.Proofs.M48.RegularSpacetime
import PoincareConjecture.Proofs.M48.RegularSliceTransport
import PoincareConjecture.Proofs.M48.RegularCylinderTransport
import PoincareConjecture.Proofs.M48.SurgeryCylinderTransport
import PoincareConjecture.Proofs.M48.RegularNoncollapse
import PoincareConjecture.Proofs.M48.SurgeryNoncollapse
import PoincareConjecture.Proofs.M48.ObservedAnalytics
import PoincareConjecture.Proofs.M48.RegularTimeAnalytics
import PoincareConjecture.Proofs.M48.RegularReference
import PoincareConjecture.Proofs.M48.StrongNeck
import PoincareConjecture.Proofs.M48.SingularInput
import PoincareConjecture.Proofs.M48.TerminalContinuation
import PoincareConjecture.Proofs.M48.NextFrontier
import PoincareConjecture.Proofs.M48.ExtensionPrefix
import PoincareConjecture.Proofs.M48.ExtensionControls
import PoincareConjecture.Proofs.M33.TerminalPolicyAtFrontier
import PoincareConjecture.Proofs.M48.TerminalPolicy

set_option autoImplicit false

universe u

namespace PoincareConjecture

theorem repairedEpochExtension : RepairedEpochExtensionTheory.{u} := by
  classical
  refine ⟨?_⟩
  intro P S A N C
  refine ⟨⟨?_⟩⟩
  intro p hp F O hstart hend hdomain L old terminal_policy controls
  let Q := Classical.choice (N.induction p hp)
  let R : SurgeryCanonicalExtension p Q := Classical.choice (C.induction p hp)
  change SurgeryEpochContinuationControls p F O Q R at controls
  obtain ⟨geom, reference, H, limit, horn, href, hr, he, hC, hA,
      htimes, hlimit, bridge, branch, O', hprogress, hbound, hsurgery,
      hfree, hfrontier, hslab, hstandard⟩ :=
    A.singular_frontier P hp old controls hstart hend hdomain L
  have full_policy : SurgeryFlowTerminalPolicyOn F F.time_domain := by
    rw [hdomain]
    simpa only [surgeryObservationInterval] using terminal_policy
  have target_policy_full := branch.conclusion.terminalPolicy full_policy
  have target_policy : SurgeryFlowTerminalPolicyOn branch.conclusion.extension.extended
      (surgeryObservationInterval O') :=
    target_policy_full.restrict O'.interval_subset
  obtain ⟨hprefix, hcanonical, hnoncollapsed⟩ :=
    branch.observedControls old controls O' hstart
      ⟨hstart.trans_lt hprogress, hbound⟩ target_policy P.m13
  refine ⟨branch.conclusion.extension,
    branch.conclusion.old_event_data,
    branch.conclusion.terminal_operation.singletonTerminalPolicy,
    O', hprogress, hbound, hsurgery,
    hfree, hfrontier, O'.interval_subset, hprefix,
    branch.conclusion.admissible, branch.conclusion.pinched,
    hstandard, ?_, hcanonical, hnoncollapsed, hslab⟩
  simpa only [branch.conclusion.extension.parameters_eq] using controls.next_kappa

end PoincareConjecture
