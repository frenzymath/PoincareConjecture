import PoincareConjecture.Proofs.M51.GlobalExtension
import PoincareConjecture.Proofs.M48.ExtensionCylinderMetric
import PoincareConjecture.Proofs.M48.RoundCylinderCongruence











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



noncomputable def globalTerminalStrongNeck
    (T : ℝ) (hT : T ∈ Q.globalSurgeryTimes)
    [Nonempty ((Q.globalFlow m13).slice T).carrier]
    [Nonempty (Q.globalSlice T).carrier]
    [Nonempty ((Q.flow (Q.representativeIndex T)).slice T).carrier]
    (i : Fin (Q.globalEventSource T hT).cap_count)
    (W : SurgeryTerminalStrongNeck (Q.flow (Q.representativeIndex T)) T
      (Q.eventStageSurgery T hT) i) :
    SurgeryTerminalStrongNeck (Q.globalFlow m13) T hT i := by
  let A := Q.globalEventSource T hT
  let D := Q.globalExtension m13 (Q.representativeIndex T)
  let d := D.pushCylinder W.cylinder
  refine ⟨d, ?_, ?_⟩
  · intro s hs ht x hx
    change Q.globalIdentify (Q.representativeIndex T)
        (T + s / (A.necks i).neck.scale⁻¹ ^ 2)
        (W.cylinder.time_subset ⟨s, hs, rfl⟩) (W.cylinder.forward s hs x) =
      (Q.globalEvent T hT).pre_identify
        ⟨T + s / (A.necks i).neck.scale⁻¹ ^ 2, ht⟩
          ((Q.globalEvent T hT).limit_identify.inverse x)
    rw [W.reference_compatibility s hs ht x hx, Q.globalEvent_pre_identify,
      Q.globalEvent_limit_inverse, Diffeomorph.symm_apply_apply]
    rfl
  · have hcomparison : RoundCylinderFamilyClose (F0.parameters.delta T)
        (Ioc (-1 : ℝ) 0)
        (fun s => if s = 0 then
          fun z v w => (A.necks i).neck.scale⁻¹ ^ 2 *
            roundCylinderPullback A.limit_metric (A.necks i).neck.coordinate_map z v w
          else surgeryCylinderPullback W.cylinder (A.necks i).neck.coordinate_map s) := by
      have hdelta := congrArg (fun P : SurgeryParameters => P.delta T)
        (Q.parameters_eq (Q.representativeIndex T))
      exact hdelta ▸ W.comparison
    apply RoundCylinderFamilyClose.congr (B' := fun s => if s = 0 then
        fun z v w => (A.necks i).neck.scale⁻¹ ^ 2 *
          roundCylinderPullback A.limit_metric (A.necks i).neck.coordinate_map z v w
        else surgeryCylinderPullback W.cylinder (A.necks i).neck.coordinate_map s)
      ?_ hcomparison
    intro s hs z hz v w
    by_cases hs0 : s = 0
    · simp only [hs0]
      rfl
    · have hs' : s ∈ Ioo (-1 : ℝ) 0 := ⟨hs.1, lt_of_le_of_ne hs.2 hs0⟩
      have hz' : z.2 ∈ Ioo (-(A.necks i).neck.epsilon⁻¹)
          (A.necks i).neck.epsilon⁻¹ := by
        simpa only [A.neck_delta, Q.parameters_eq] using hz
      have hcoord : (A.necks i).neck.coordinate_map z ∈ (A.necks i).neck.carrier := by
        have h := (A.necks i).neck.coordinate_map_eq (z.1, ⟨z.2, hz'⟩)
        exact h ▸ ((A.necks i).neck.coordinate (z.1, ⟨z.2, hz'⟩)).property
      simp only [if_neg hs0, surgeryCylinderPullback, dif_pos hs']
      exact D.pushCylinder_pullbackInner W.cylinder
        (A.necks i).neck.carrier_open s hs' _ hcoord _ _

end PoincareConjecture.M51.CompletedStageChain
