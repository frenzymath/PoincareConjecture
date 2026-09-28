import PoincareConjecture.Proofs.M51.EmptyAdmissible
import PoincareConjecture.Proofs.M51.EmptyControls
import PoincareConjecture.Proofs.M51.EmptyPolicy
import PoincareConjecture.Definitions.M51GlobalSchedule

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

universe u

namespace PoincareConjecture.M51Empty

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

end PoincareConjecture.M51Empty
