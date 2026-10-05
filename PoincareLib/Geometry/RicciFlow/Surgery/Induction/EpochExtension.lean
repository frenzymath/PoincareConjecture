import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Construction.ContinuationPolicy
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochTheory
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Prefix.PrefixControls
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Analytics.RicciNormTransport
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Analytics.ScalarEvolution
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Analytics.LimitCalibration
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.History.RegularHistory
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.History.RegularSpacetime
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.History.RegularSliceTransport
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.History.RegularCylinderTransport
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Cylinders.SurgeryCylinderTransport
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.History.RegularNoncollapse
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Cylinders.SurgeryNoncollapse
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Analytics.ObservedAnalytics
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.History.RegularTimeAnalytics
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.History.RegularReference
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Canonical.StrongNeck
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Terminal.SingularInput
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Terminal.TerminalContinuation
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Terminal.NextFrontier
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Extension.ExtensionPrefix
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Extension.ExtensionControls
import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Construction.TerminalPolicy
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Terminal.TerminalPolicy

/-!
# M48 one-step epoch extension
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-
Natural-language theorem: fix the predecessor services, the calibrated
setup and seeds, and M48AnalyticCalibration retaining the actual M47 component
estimate and all coefficient/cutoff bounds. Choose the M46/M47 packages for
that final setup. For any compatible finite prefix
with index i > 0, consider a flow with exact
time domain [0,H), T_i <= H < T_(i+1), and a preterminal smooth slab with
curvature unbounded at H. Suppose its schedule prefix is controlled, its
current canonical and noncollapsing properties hold at the selected radius,
the old observation satisfies the terminal policy,
and its total parameter profiles obey the selected scales on the next epoch
and overlap. The observation uses the calibrated standard-cap model. There is an actual
changing-carrier extension performing surgery at H and an observation
H < H' <= T_(i+1), with no surgery in (H,H'). If H' is before the epoch
boundary, the extended time domain is exactly [0,H') and a preterminal slab
starts at H and has singular frontier H'. Otherwise the observation is at
the epoch boundary, without requiring the returned flow to end there.
If its domain ends at that boundary, the actual preterminal slab starting
at H is retained there as well.

The extension preserves old-prefix controls and has whole-domain
admissibility and pinching. The observed interval satisfies the selected M46
noncollapsing bound and the selected M47 canonical-neighborhood property.
The stored analytic coefficient applies at the auxiliary M31 radius through
the retained component and model estimates. `M48AnalyticCalibration.continuation`
constructs it on the actual observation from its existing controls.
`regular_gradient` and `regular_time_derivative` transfer both estimates to
the same selected history at `historyRadius`; the strict threshold margin
permits time-derivative continuity across retained old events.
`frontier_history_scale` identifies the unchanged stored height and its strict
auxiliary-radius guard. No flow estimate is assumed.
`regular_reference_exists` constructs M31's actual final ordinary reference
on this same history, retaining the original slab metric and connection.
`RegularGuards` supplies its finite singular catalog, regular-slice compactness
and calibrated doubled-epsilon bound.
`M33RegularHistoryData.canonical_neck` transports the whole original strong-neck
cylinder on this same history, including retained old events, with unchanged
scale and strict comparison bound. `canonical_control` also constructs the
static cap/component/round branches with the original constants and models.
`M48AnalyticCalibration.singular_input` assembles every M31 input field
on this history. `regular_limit` produces the ordinary reference and applies
the stored calibrated limit service, retaining the same limit in its horn wrapper.
`singular_continuation` constructs M33's actual input and terminal bridge from
that one selected limit. Its core is the terminal scalar sublevel, the height
is the stored M32 choice, and local surgery uses the retained M36 operation
with the flow's exact constants. It applies M33 to these literal values.
`singular_frontier` then observes this same maximal ordinary restart at its
finite endpoint or the epoch boundary, retaining the selected standard flow.
It exports the actual next slab whenever the returned domain ends there,
including equality with the epoch boundary, without truncating a longer flow.
`RepairedBranchContinuationData.prefixControls` carries every old epoch entry
to this actual branch. It pushes whole strong-neck cylinders and pulls tested
closed backward balls through the extension isometries, retaining the positive
component exception, the original scale, and all parameter identities.

Source: Morgan--Tian, Theorem 15.9 and its inductive outline, printed
pp. 363--366, Proposition 16.1, Proposition 17.1, and the continuation
construction of Section 17.2, printed pp. 409--410. The checked application
supplies M33's actual maximal surgery/restart branch and next observation,
then applies the exact selected M47 and M46 services to that same branch.
Its supplied M33 service also constructs the actual generalized regular
history on [0,H) through
`M48Predecessors.regularHistory`. The checked M11 interval realization and
supplied M12 service construct the same-carrier intrinsic Ricci geometry
through `M48Predecessors.regularSpacetime`. M13
identifies its scalar curvature, full curvature norm, negative curvature part
and volume with the actual surgery history through `RegularSliceTransport`;
full-slice distance retains the nonsurgery-time guard. `RegularCylinderTransport`
places raw history cylinders and their exact metrics on this same realization.
`SurgeryCylinderTransport` applies the guarded M33 lift to the same history;
`RegularNoncollapse` transfers a supplied M15 predicate to the raw generalized
flow with the same constant, restricting half-open windows through smaller radii.
`SurgeryNoncollapse` passes that estimate to the actual surgery flow, retaining
the positive-component exclusion. M33's checked metric helpers identify balls
when the full ambient ball is retained; the volume transfer needs only their
one-sided inclusion. Actual M15 configurations are internal obligations of
the supplied M46/M47 services. `observedControls` transports the prescribed
profiles to this extension, applies M47, and then applies M46 with its cutoff.
No additional admission or analytic premise is used by this assembly.
The M33 terminal operation also supplies a checked terminal-policy witness on
the singleton newly-created frontier event `{O.H}`. The same branch retains
M33's primitive old-event preservation. `observedTerminalPolicy` combines
these outputs with existing old policy on the returned observation; it does
not create policy for arbitrary earlier events or an unobserved future.
The historical M31/M36/M43 predecessor fields remain compatibility inputs;
the actual selected limit and surgery operations are retained by the setup.
This singular step does not establish a closed continuation
chain, local finiteness, a global schedule, or an endpoint theorem. The
bounded prefix correction and exact Q/R selection are reviewed in
`reviews/contracts/2026-09-15-m45-finite-prefix-round1.md`.
-/
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

end PoincareMT
