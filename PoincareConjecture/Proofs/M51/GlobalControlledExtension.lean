import PoincareConjecture.Proofs.M51.GlobalAdmissible
import PoincareConjecture.Proofs.M51.GlobalExtension
import PoincareConjecture.Proofs.M51.GlobalProfileControls
import PoincareConjecture.Proofs.M51.GlobalVolumeAssembly
import PoincareConjecture.Definitions.M51GlobalSchedule











set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.M51.CompletedStageChain

variable {S : RepairedControlledSchedulesData.{u}}
  {N : RepairedNoncollapseInductionData S}
  {C : RepairedCanonicalInductionData S N}
  {F₀ : SurgeryFlowData.{u}} {k : ℕ}
  (Q : CompletedStageChain S N C F₀ k)
  (m13 : GeneralizedParabolicRescalingTheory.{u} 3)
  (F50 : RepairedFinitePrefixTheory.{u})
  (d : ℝ) (hd : (M51Numerical.schedule S N C).Delta 0 ≤ d)
  (losses : ∀ (F : SurgeryFlowData.{u}) (V : RepairedVolumeLossControls F),
    F.standard_initial = S.standard_initial → F.local_constants = S.constants →
    (∀ t ∈ F.surgery_times, F.parameters.delta t ≤ d) →
    Nonempty (RepairedVolumeLossData F V))
  (delta : ℝ → ℝ)
  (hdelta : ∀ t, 0 ≤ t → F₀.parameters.delta t = delta t)
  (hprofiles : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
    F₀.parameters.r t = (M51Numerical.schedule S N C).r j ∧
    F₀.parameters.kappa t = (M51Numerical.schedule S N C).kappa j ∧
    F₀.parameters.h t = S.setup.selector.h
      (delta t * F₀.parameters.r t) (delta t))
  (hcut : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
    delta t ≤ (M51Numerical.schedule S N C).Delta j)


noncomputable def controlledExtension :
    RepairedGlobalControlledExtension (M51Numerical.schedule S N C) F₀ := by
  let E := Q.inputExtension m13
  have htarget : E.extended = Q.globalFlow m13 := Q.inputExtension_extended m13
  have hadmissible : SurgeryFlowAdmissible E.extended := by
    rw [htarget]
    exact Q.globalFlow_admissible m13
  have hpinched : SurgeryFlowPinched E.extended := by
    rw [htarget]
    exact Q.globalFlow_pinched m13
  have hpolicy : SurgeryFlowTerminalPolicyOn E.extended E.extended.time_domain := by
    rw [htarget]
    exact Q.globalFlow_terminalPolicy m13
  have hgeometry := Q.profile_controls_of_extensions m13 (Q.globalFlow m13)
    (Q.globalExtension m13) (Q.globalExtension_extended m13)
  have hcanonical : SurgeryCanonicalAssumption E.extended := by
    rw [htarget]
    exact hgeometry.1
  have hnoncollapsed : SurgeryNoncollapsed E.extended := by
    rw [htarget]
    exact hgeometry.2
  have hagreement : ∀ j t, t ∈ surgeryEpochEntry j → t ∈ E.extended.time_domain →
      E.extended.parameters.r t = (M51Numerical.schedule S N C).r j ∧
      E.extended.parameters.kappa t = (M51Numerical.schedule S N C).kappa j ∧
      E.extended.parameters.delta t ≤ (M51Numerical.schedule S N C).Delta j ∧
      E.extended.parameters.h t = (M51Numerical.schedule S N C).setup.selector.h
        (E.extended.parameters.delta t * E.extended.parameters.r t)
        (E.extended.parameters.delta t) := by
    intro j t ht htF
    have ht0 := E.extended.time_domain_nonnegative htF
    have hprofile := hprofiles j t ht ht0
    rw [E.parameters_eq, hdelta t ht0]
    exact ⟨hprofile.1, hprofile.2.1, hcut j t ht ht0, hprofile.2.2⟩
  have hstandard : E.extended.standard_initial = S.standard_initial :=
    E.standard_initial_eq.trans
      (((Q.standard_initial_eq 0).symm.trans (Q.standard_initial_setup_eq 0)).trans
        S.setup_standard_initial_eq)
  have hconstants : E.extended.local_constants = S.constants :=
    E.local_constants_eq.trans
      ((Q.local_constants_eq 0).symm.trans (Q.local_constants_setup_eq 0))
  have volume := selected_global_volume S N C m13 F50 d hd losses E.extended
    hstandard hconstants hadmissible hpinched
    (fun j t hj ht => (hagreement j t hj ht).2.2.1)
  let V := Classical.choose volume
  let finite : RepairedFinitePrefixData E.extended
      (globalVolumeControls E.extended m13 hadmissible hpinched) V :=
    Classical.choice (Classical.choose_spec volume)
  exact {
    extension := E
    time_domain_eq := by rw [htarget]; exact Q.globalFlow_time_domain m13
    admissible := hadmissible
    terminal_policy := hpolicy
    pinched := hpinched
    canonical := hcanonical
    noncollapsed := hnoncollapsed
    schedule_agreement := hagreement
    local_finite := finite.local_finite
    no_finite_accumulation := fun T _ => finite.no_finite_accumulation T }


theorem controlledExtension_extension :
    (Q.controlledExtension m13 F50 d hd losses delta hdelta hprofiles hcut).extension =
      Q.inputExtension m13 := rfl


theorem controlledExtension_extended :
    (Q.controlledExtension m13 F50 d hd losses delta hdelta hprofiles hcut).extension.extended =
      Q.globalFlow m13 := Q.inputExtension_extended m13

end PoincareConjecture.M51.CompletedStageChain
