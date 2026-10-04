import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Terminal.TerminalBridge

/-!
# Apply M33 to the constructed M48 terminal bridge

From the actual one-step input, select one regular history, one M31 input
and limit, then construct the core/bridge and apply the supplied M33 service.
This is the surgery/restart application in Section 17.2, pp. 409--410.
`NextFrontier.lean` observes its maximal ordinary restart. Returned
canonical/noncollapse controls remain separate M48 obligations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

universe u

namespace PoincareMT.M48AnalyticCalibration

/-- Produce the same-history input, literal terminal bridge and actual M33
continuation from the existing M48 assumptions. All six M31 data identities
and the full selected-limit identity remain available to later consumers. -/
theorem singular_continuation
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
                Nonempty (RepairedBranchContinuationData
                  (A.continuationInput hp old controls hstart hend hdomain L
                    (m48TerminalCore H horn (F.parameters.delta O.H * F.parameters.r O.H)))) := by
  obtain ⟨R⟩ := P.regularSpacetime L
  obtain ⟨reference, H, href, hr, he, hC, hA, htimes, limit, horn, hlimit, _haccuracy⟩ :=
    A.regular_limit P hp old controls R
  let bridge := A.terminalBridge hp old controls hstart hend hdomain
    reference H href hr he hC hA limit horn hlimit
  exact ⟨R, reference, H, limit, horn, href, hr, he, hC, hA, htimes, hlimit,
    bridge, P.m33.continuation _ H limit horn bridge⟩

end PoincareMT.M48AnalyticCalibration
