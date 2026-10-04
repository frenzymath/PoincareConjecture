import PoincareLib.Geometry.RicciFlow.Surgery.Global.ScheduleData
import PoincareLib.Geometry.RicciFlow.Surgery.GlobalSchedule.Zero.ZeroCapDiscard
import PoincareLib.Geometry.RicciFlow.Surgery.GlobalSchedule.Epoch.EpochCoverage

/-!
# M49 controls on a given M51 prefix

Use the same raw flow and its entire excluded-horizon observation. The
zero-cap component input comes from actual event maximality. Only numerical
parameter profiles, never geometric slices, are read beyond the old domain.
-/

set_option autoImplicit false

universe u

namespace PoincareMT.RepairedGlobalControlledPrefix

variable {K : MetricSurgeryConstants} {S : GlobalSurgerySchedule K}
    {delta : ℝ → ℝ} {F : SurgeryFlowData.{u}} {H : ℝ}
    (P : RepairedGlobalControlledPrefix S delta F H)

include P

/-- The excluded endpoint is allowed as an observation horizon. -/
def observation : SurgeryObservation F where
  H := H
  H_pos := P.horizon_pos
  interval_subset := by rw [P.time_domain_eq]
  standard_flow := P.standard_initial_eq ▸ S.setup.standard_flow

/-- The actual flow supplies the event predicates required by M49. -/
theorem volumeControls (H13 : GeneralizedParabolicRescalingTheory.{u} 3) :
    RepairedVolumeLossControls F :=
  ⟨P.admissible, P.pinched, F.nonemptyEventPreInterval,
    F.vanishingEventPreInterval, F.zeroCapDiscard H13⟩

theorem observedVolumeControls (H13 : GeneralizedParabolicRescalingTheory.{u} 3) :
    RepairedObservedVolumeControls F P.observation where
  pinched := fun t ht => P.pinched t (P.observation.interval_subset ht)
  strong_boundaries := fun T hT _ => P.admissible.strong_boundaries T hT
  strong_disappearing := fun T hT _ => P.admissible.strong_disappearing T hT
  strong_vanishing := fun T hT _ => P.admissible.strong_vanishing T hT
  nonempty_pre_interval := F.nonemptyEventPreInterval
  vanishing_pre_interval := F.vanishingEventPreInterval
  zero_cap_discard := F.zeroCapDiscard H13

/-- One bound for the global seed bounds every event's actual delta. -/
theorem event_delta_le (d : ℝ) (hd : S.Delta 0 ≤ d)
    (hdelta : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t → delta t ≤ S.Delta j)
    {t : ℝ} (ht : t ∈ F.surgery_times) : F.parameters.delta t ≤ d := by
  have ht0 := F.time_domain_nonnegative (F.surgery_times_subset ht)
  obtain ⟨j, hj⟩ := exists_surgeryEpochEntry ht0
  rw [P.delta_eq t ht0]
  exact (hdelta j t hj ht0).trans ((S.Delta_antitone (Nat.zero_le j)).trans hd)

/-- The prescribed future profiles identify the common horizon height;
raw parameter monotonicity then bounds every earlier actual height. -/
theorem height_lower_bound {B : ℝ} {k : ℕ} (hB : 0 ≤ B)
    (hk : B ∈ surgeryEpochEntry k) {t : ℝ} (ht : 0 ≤ t) (htB : t ≤ B) :
    S.setup.selector.h (delta B * S.r k) (delta B) ≤ F.parameters.h t := by
  have hprofile := P.schedule_agreement k B hk hB
  have heq : F.parameters.h B = S.setup.selector.h (delta B * S.r k) (delta B) := by
    rw [hprofile.2.2, hprofile.1]
  rw [← heq]
  exact F.parameters.h_antitone ht hB htB

end PoincareMT.RepairedGlobalControlledPrefix
