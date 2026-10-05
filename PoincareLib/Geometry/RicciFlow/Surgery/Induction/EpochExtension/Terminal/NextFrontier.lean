import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Terminal.TerminalContinuation
import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Construction.MaximalRestart

/-!
# The next frontier of the actual M48 restart

Apply M33 once to the selected terminal bridge, then observe that same
maximal restart at its next singular endpoint or the epoch boundary.
Section 17.2, pp. 409--410. Old-prefix and returned geometric controls are
separate M48 obligations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

universe u

namespace PoincareMT.M48AnalyticCalibration

/-- Retain the literal M33 branch, all selected M31 identities, and a
calibrated observation on that branch. An excluded endpoint supplies its
actual preterminal slab even at equality with the epoch boundary. -/
theorem singular_frontier
    {S : RepairedControlledSchedulesData.{u}} (A : M48AnalyticCalibration S)
    (P : M48Predecessors.{u})
    {p : SurgeryParameterPrefix S.constants} {F : SurgeryFlowData.{u}}
    {O : SurgeryObservation F} (hp : S.SeedCompatible p)
    (old : SurgeryPrefixControls p F O)
    {Q : SurgeryNoncollapseExtension.{u} p} {N : SurgeryCanonicalExtension p Q}
    (controls : SurgeryEpochContinuationControls p F O Q N)
    (hstart : surgeryEpochStart p.i ≤ O.H)
    (hend : O.H < surgeryEpochStart (p.i + 1))
    (hdomain : F.time_domain = Ico 0 O.H) (L : RepairedPreterminalSlab F O.H) :
    ∃ R : M48RegularSpacetimeData L,
      ∃ reference : M48RegularReferenceData L R.history,
        ∃ H : SingularTimeAssumptions R.history.generalized O.H (F.slice L.start).carrier,
          ∃ limit : RepairedSingularRegularLimitData H,
            ∃ horn : RepairedHornSelectionData H,
              H.reference = reference.reference ∧ H.r₀ = A.historyRadius N.rNext ∧
              H.epsilon = S.setup.epsilon ∧ H.constant = S.setup.C ∧
              H.analytic_constant = S.calibration.analytic_constant ∧
              H.singularTimes = L.singularCatalog ∧ horn.limit = limit ∧
              ∃ _bridge : RepairedContinuationLimitBridge H limit horn
                  (A.continuationInput hp old controls hstart hend hdomain L
                    (m48TerminalCore H horn (F.parameters.delta O.H * F.parameters.r O.H))),
                ∃ branch : RepairedBranchContinuationData
                    (A.continuationInput hp old controls hstart hend hdomain L
                      (m48TerminalCore H horn (F.parameters.delta O.H * F.parameters.r O.H))),
                  ∃ O' : SurgeryObservation branch.conclusion.extension.extended,
                    O.H < O'.H ∧ O'.H ≤ surgeryEpochStart (p.i + 1) ∧
                    O.H ∈ branch.conclusion.extension.extended.surgery_times ∧
                    Disjoint branch.conclusion.extension.extended.surgery_times
                      (Ioo O.H O'.H) ∧
                    (O'.H < surgeryEpochStart (p.i + 1) →
                      branch.conclusion.extension.extended.time_domain = Ico 0 O'.H ∧
                        ∃ next : RepairedPreterminalSlab
                            branch.conclusion.extension.extended O'.H,
                          next.start = O.H) ∧
                    (branch.conclusion.extension.extended.time_domain = Ico 0 O'.H →
                      ∃ next : RepairedPreterminalSlab
                          branch.conclusion.extension.extended O'.H,
                        next.start = O.H) ∧
                    HEq O'.standard_flow p.setup.standard_flow := by
  obtain ⟨R, reference, H, limit, horn, href, hr, he, hC, hA, htimes, hlimit,
      bridge, ⟨branch⟩⟩ :=
    A.singular_continuation P hp old controls hstart hend hdomain L
  obtain ⟨U, hprogress, hbound, hinterval, hfree, hfrontier, hslab⟩ :=
    branch.conclusion.frontier_before hend
  have hstandard : branch.conclusion.extension.extended.standard_initial =
      p.setup.standard_initial :=
    branch.conclusion.extension.standard_initial_eq.trans old.standard_initial_eq
  let O' : SurgeryObservation branch.conclusion.extension.extended :=
    { H := U
      H_pos := O.H_pos.trans hprogress
      interval_subset := hinterval
      standard_flow := hstandard ▸ p.setup.standard_flow }
  refine ⟨R, reference, H, limit, horn, href, hr, he, hC, hA, htimes, hlimit,
    bridge, branch, O', hprogress, hbound, branch.conclusion.surgery_at_terminal,
    hfree, ?_, hslab, ?_⟩
  · intro hlt
    exact ⟨hfrontier hlt, hslab (hfrontier hlt)⟩
  · exact eqRec_heq _ _

end PoincareMT.M48AnalyticCalibration
