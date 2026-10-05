import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Branch
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.NoncollapseData
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.CanonicalData

/-!
Adapted from Mapher `PoincareMT/Definitions/M48EpochExtension.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# M48 repaired one-step epoch extension data

The input ends at an actual singular frontier strictly before the next epoch
boundary. The extension performs surgery at that old frontier and reaches
the next singular frontier, or is observed at the epoch boundary. A returned
singular frontier is excluded from the extended time domain and is the end of
the slab beginning at the old frontier. The same slab is retained when the
finite endpoint equals the epoch boundary. A longer returned flow is not
truncated at that boundary.

The selected M46 noncollapsing and M47 canonical properties, admissibility,
pinching, and the selected standard-flow decoration are actual output
predicates. Scalar time-derivative control remains a separate analytic
service.
The checked M48 assembly constructs the restart from its calibrated services
and applies the selected M47/M46 outputs to that same flow and observation.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-- Primitive guards for the actual current flow and its total parameter
profiles. The full future epoch and overlap are needed because an extension
preserves `F.parameters`, including their values beyond the current domain.
The selected geometric controls are restricted to the current observation;
the profile equalities below are numerical guards through the next epoch and
overlap. Scalar time-derivative control remains a separate analytic service. -/
structure SurgeryEpochContinuationControls {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) (F : SurgeryFlowData.{u})
    (O : SurgeryObservation F) (Q : SurgeryNoncollapseExtension.{u} p)
    (R : SurgeryCanonicalExtension p Q) : Prop where
  canonical : SurgeryCanonicalOn F (surgeryObservationInterval O) R.rNext
  noncollapsed :
    SurgeryNoncollapsedAssumptionOn F (surgeryObservationInterval O)
  next_r : ∀ t ∈ surgeryEpoch p.i, F.parameters.r t = R.rNext
  /-- Definition 15.7 uses the exact selected step value. -/
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
      -- Retain the same M33 branch's old geometry and new frontier policy.
      -- These transport existing policy; raw earlier events need not have it.
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

end PoincareMT
