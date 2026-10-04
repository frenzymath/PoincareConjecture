import PoincareLib.Geometry.RicciFlow.Surgery.GlobalSchedule.Empty.EmptyAdmissible
import PoincareLib.Geometry.RicciFlow.Surgery.GlobalSchedule.Empty.EmptyControls
import PoincareLib.Geometry.RicciFlow.Surgery.GlobalSchedule.Empty.EmptyPolicy
import PoincareLib.Geometry.RicciFlow.Surgery.Global.ScheduleData

/-!
# The controlled empty branch of M51

Morgan--Tian Section 17.2, p. 409. An included empty slice completes the
given-flow branch on all nonnegative times, with the original numerical
profiles, actual old events and geometric controls. This does not construct
the normalized initial flow or iterate the nonempty branch.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

universe u

namespace PoincareMT.M51Empty

noncomputable def controlledExtension
    (m13 : GeneralizedParabolicRescalingTheory.{u} 3)
    {K : MetricSurgeryConstants} {S : GlobalSurgerySchedule K}
    {delta : ℝ → ℝ} {F : SurgeryFlowData.{u}} {H a : ℝ}
    (P : RepairedGlobalControlledPrefix S delta F H)
    (ha : a ∈ F.time_domain) [IsEmpty (F.slice a).carrier]
    (hdelta : ∀ j : ℕ, ∀ t ∈ surgeryEpochEntry j,
      0 ≤ t → delta t ≤ S.Delta j) :
    RepairedGlobalControlledExtension S F where
  extension := extension F ha
  time_domain_eq := rfl
  admissible := admissible F ha m13 P.admissible
  terminal_policy := terminalPolicy F ha P.terminal_policy
  pinched := pinched F ha P.pinched
  canonical := canonical F ha m13 P.canonical
  noncollapsed := noncollapsed F ha m13 P.noncollapsed
  schedule_agreement := by
    intro j t ht ht0
    rcases P.schedule_agreement j t ht ht0 with ⟨hr, hk, hh⟩
    change F.parameters.r t = S.r j ∧ F.parameters.kappa t = S.kappa j ∧
      F.parameters.delta t ≤ S.Delta j ∧
      F.parameters.h t = S.setup.selector.h
        (F.parameters.delta t * F.parameters.r t) (F.parameters.delta t)
    rw [P.delta_eq t ht0]
    exact ⟨hr, hk, hdelta j t ht ht0, hh⟩
  local_finite := fun _ _ => (flow_events_finite F ha).subset inter_subset_left
  no_finite_accumulation := fun _ _ =>
    ⟨1, by norm_num, (flow_events_finite F ha).subset inter_subset_left⟩

end PoincareMT.M51Empty
