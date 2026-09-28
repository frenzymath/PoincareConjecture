import PoincareConjecture.Definitions.M33BranchContinuation
import PoincareConjecture.Definitions.M46NoncollapseInduction
import PoincareConjecture.Definitions.M47CanonicalInduction




















set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture







structure SurgeryEpochContinuationControls {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) (F : SurgeryFlowData.{u})
    (O : SurgeryObservation F) (Q : SurgeryNoncollapseExtension.{u} p)
    (R : SurgeryCanonicalExtension p Q) : Prop where
  canonical : SurgeryCanonicalOn F (surgeryObservationInterval O) R.rNext
  noncollapsed :
    SurgeryNoncollapsedAssumptionOn F (surgeryObservationInterval O)
  next_r : ∀ t ∈ surgeryEpoch p.i, F.parameters.r t = R.rNext

  next_kappa : ∀ t ∈ surgeryEpoch p.i, F.parameters.kappa t = Q.kappaNew
  next_h : ∀ t ∈ surgeryEpoch p.i,
    F.parameters.h t = p.setup.selector.h
      (F.parameters.delta t * F.parameters.r t) (F.parameters.delta t)
  overlap_delta : ∀ t ∈ overlapInterval p, F.parameters.delta t ≤ R.deltaNext

structure RepairedEpochExtensionData
    (S : RepairedControlledSchedulesData.{u})
    (N : RepairedNoncollapseInductionData.{u} S)
    (C : RepairedCanonicalInductionData.{u} S N) where
  extension_progress : ∀ (p : SurgeryParameterPrefix S.constants)
    (hp : S.SeedCompatible p),
    ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
    surgeryEpochStart p.i ≤ O.H →
    O.H < surgeryEpochStart (p.i + 1) →
    F.time_domain = Set.Ico 0 O.H →
    RepairedPreterminalSlab F O.H →
    SurgeryPrefixControls p F O →
    SurgeryFlowTerminalPolicyOn F (surgeryObservationInterval O) →
    SurgeryEpochContinuationControls p F O
      (Classical.choice (N.induction p hp))
      (Classical.choice (C.induction p hp)) →


      ∃ E : SurgeryFlowExtension F,
        ∃ _old_event_data : M33OldEventDataPreservation E,
        ∃ _terminal_policy : SurgeryFlowTerminalPolicyOn E.extended ({O.H} : Set ℝ),
        ∃ O' : SurgeryObservation E.extended,
          O.H < O'.H ∧
          O'.H ≤ surgeryEpochStart (p.i + 1) ∧
          O.H ∈ E.extended.surgery_times ∧
          Disjoint E.extended.surgery_times (Set.Ioo O.H O'.H) ∧
          (O'.H < surgeryEpochStart (p.i + 1) →
            E.extended.time_domain = Set.Ico 0 O'.H ∧
              ∃ next : RepairedPreterminalSlab E.extended O'.H,
                next.start = O.H) ∧
          Set.Ico 0 O'.H ⊆ E.extended.time_domain ∧
          SurgeryPrefixControls p E.extended O' ∧
          SurgeryFlowAdmissible E.extended ∧
          SurgeryFlowPinched E.extended ∧
          HEq O'.standard_flow p.setup.standard_flow ∧
          (∀ t ∈ surgeryEpoch p.i,
            E.extended.parameters.kappa t =
              (Classical.choice (N.induction p hp)).kappaNew) ∧
          SurgeryCanonicalOn E.extended (surgeryObservationInterval O')
            (Classical.choice (C.induction p hp)).rNext ∧
          SurgeryNoncollapsedOn E.extended (surgeryObservationInterval O')
            (Classical.choice (N.induction p hp)).kappaNew ∧
          (E.extended.time_domain = Set.Ico 0 O'.H →
            ∃ next : RepairedPreterminalSlab E.extended O'.H,
              next.start = O.H)

end PoincareConjecture
