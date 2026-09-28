import PoincareConjecture.Proofs.M48.TerminalBridge











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

universe u

namespace PoincareConjecture.M48AnalyticCalibration




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

end PoincareConjecture.M48AnalyticCalibration
