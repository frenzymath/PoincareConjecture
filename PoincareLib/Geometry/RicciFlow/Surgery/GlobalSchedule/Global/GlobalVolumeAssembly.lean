import PoincareLib.Geometry.RicciFlow.Surgery.GlobalSchedule.Numerical.NumericalSchedule
import PoincareLib.Geometry.RicciFlow.Surgery.GlobalSchedule.Epoch.EpochCoverage
import PoincareLib.Geometry.RicciFlow.Surgery.GlobalSchedule.Zero.ZeroCapDiscard
import PoincareLib.Geometry.RicciFlow.Surgery.Volume.FinitePrefixTheory

/-!
# The retained loss service on the actual global flow

Use the cutoff chosen before induction, build the primitive event controls
on this flow, and pass its selected certificate unchanged to M50.
Source: Morgan--Tian Section 17.2, printed pp. 409-411.
-/

set_option autoImplicit false

open Set

universe u

namespace PoincareMT.M51

/-- The actual raw flow supplies the primitive event predicates needed for volume loss. -/
theorem globalVolumeControls (F : SurgeryFlowData.{u})
    (H13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (admissible : SurgeryFlowAdmissible F) (pinched : SurgeryFlowPinched F) :
    RepairedVolumeLossControls F :=
  ⟨admissible, pinched, F.nonemptyEventPreInterval,
    F.vanishingEventPreInterval, F.zeroCapDiscard H13⟩

/-- Apply the retained loss service and M50 to the same flow and the same loss certificate. -/
theorem selected_global_volume
    (S : RepairedControlledSchedulesData.{u})
    (N : RepairedNoncollapseInductionData S)
    (C : RepairedCanonicalInductionData S N)
    (H13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (F50 : RepairedFinitePrefixTheory.{u})
    (d : ℝ) (hd : (M51Numerical.schedule S N C).Delta 0 ≤ d)
    (losses : ∀ (F : SurgeryFlowData.{u}) (V : RepairedVolumeLossControls F),
      F.standard_initial = S.standard_initial → F.local_constants = S.constants →
      (∀ t ∈ F.surgery_times, F.parameters.delta t ≤ d) →
      Nonempty (RepairedVolumeLossData F V))
    (F : SurgeryFlowData.{u})
    (hstandard : F.standard_initial = S.standard_initial)
    (hconstants : F.local_constants = S.constants)
    (admissible : SurgeryFlowAdmissible F) (pinched : SurgeryFlowPinched F)
    (hdelta : ∀ j t, t ∈ surgeryEpochEntry j → t ∈ F.time_domain →
      F.parameters.delta t ≤ (M51Numerical.schedule S N C).Delta j) :
    ∃ V : RepairedVolumeLossData F (globalVolumeControls F H13 admissible pinched),
      Nonempty (RepairedFinitePrefixData F (globalVolumeControls F H13 admissible pinched) V) := by
  have hbound : ∀ t ∈ F.surgery_times, F.parameters.delta t ≤ d := by
    intro t ht
    have htF := F.surgery_times_subset ht
    obtain ⟨j, hj⟩ := exists_surgeryEpochEntry (F.time_domain_nonnegative htF)
    exact (hdelta j t hj htF).trans
      (((M51Numerical.schedule S N C).Delta_antitone (Nat.zero_le j)).trans hd)
  obtain ⟨V⟩ := losses F (globalVolumeControls F H13 admissible pinched)
    hstandard hconstants hbound
  exact ⟨V, F50.finite_prefix F (globalVolumeControls F H13 admissible pinched) V⟩

end PoincareMT.M51
