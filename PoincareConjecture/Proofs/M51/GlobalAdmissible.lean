import PoincareConjecture.Proofs.M51.GlobalTerminalNeck
import PoincareConjecture.Proofs.M48.ExtensionCanonical

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M51.CompletedStageChain

variable {S : RepairedControlledSchedulesData.{u}}
  {N : RepairedNoncollapseInductionData S}
  {C : RepairedCanonicalInductionData S N}
  {F0 : SurgeryFlowData.{u}} {k : ℕ}
  (Q : CompletedStageChain S N C F0 k)
  (m13 : GeneralizedParabolicRescalingTheory.{u} 3)

theorem globalFlow_admissible : SurgeryFlowAdmissible (Q.globalFlow m13) := by
  constructor
  · intro T hT hne i
    let : Nonempty (Q.globalSlice T).carrier := hne
    let := Q.eventStageNonempty T hT
    obtain ⟨W⟩ := (Q.old_controls (Q.representativeIndex T)).admissible.strong_boundaries
      T (Q.eventStageSurgery T hT) i
    exact ⟨Q.globalTerminalStrongNeck m13 T hT i W⟩
  · intro T hT hne t hstart x hx
    let : Nonempty (Q.globalSlice T).carrier := hne
    let := Q.eventStageNonempty T hT
    let A := Q.globalEventSource T hT
    let p := Q.globalEventInitialMap T hT
    have hnot : p.symm x ∉ interior A.retained_pre := by
      intro hxold
      apply hx
      change x ∈ interior (Q.globalEvent T hT).retained_pre
      rw [Q.globalEvent_retained_pre]
      change x ∈ interior (p.toHomeomorph '' A.retained_pre)
      rw [← p.toHomeomorph.image_interior]
      exact ⟨p.symm x, hxold, p.apply_symm_apply x⟩
    have hold := (Q.globalExtension m13 (Q.representativeIndex T)).canonical_control m13
      t.1 (Q.globalEventPreTime T hT t) (A.pre_identify t (p.symm x))
      (Q.flow (Q.representativeIndex T)).parameters.epsilon
      (Q.flow (Q.representativeIndex T)).parameters.C
      ((Q.old_controls (Q.representativeIndex T)).admissible.strong_disappearing T
        (Q.eventStageSurgery T hT) t hstart (p.symm x) hnot)
    change SurgeryCanonicalControl (Q.globalFlow m13) t.1
      (((Q.globalFlow m13).event T hT).pre_identify t x)
      (Q.flow (Q.representativeIndex T)).parameters.epsilon
      (Q.flow (Q.representativeIndex T)).parameters.C at hold
    have hepsilon := congrArg SurgeryParameters.epsilon
      (Q.parameters_eq (Q.representativeIndex T))
    have hconstant := congrArg SurgeryParameters.C
      (Q.parameters_eq (Q.representativeIndex T))
    exact hepsilon ▸ hconstant ▸ hold
  · intro T hT hempty t hstart x
    let : IsEmpty (Q.globalSlice T).carrier := hempty
    let := Q.eventStageIsEmpty T hT
    let A := Q.globalVanishingSource T hT
    let p := Q.globalVanishingInitialMap T hT
    have hold := (Q.globalExtension m13 (Q.representativeIndex T)).canonical_control m13
      t.1 (Q.globalVanishingPreTime T hT t) (A.pre_identify t (p.symm x))
      (Q.flow (Q.representativeIndex T)).parameters.epsilon
      (Q.flow (Q.representativeIndex T)).parameters.C
      ((Q.old_controls (Q.representativeIndex T)).admissible.strong_vanishing T
        (Q.eventStageSurgery T hT) t hstart (p.symm x))
    change SurgeryCanonicalControl (Q.globalFlow m13) t.1
      (((Q.globalFlow m13).vanishing_event T hT).pre_identify t x)
      (Q.flow (Q.representativeIndex T)).parameters.epsilon
      (Q.flow (Q.representativeIndex T)).parameters.C at hold
    have hepsilon := congrArg SurgeryParameters.epsilon
      (Q.parameters_eq (Q.representativeIndex T))
    have hconstant := congrArg SurgeryParameters.C
      (Q.parameters_eq (Q.representativeIndex T))
    exact hepsilon ▸ hconstant ▸ hold

end PoincareConjecture.M51.CompletedStageChain
