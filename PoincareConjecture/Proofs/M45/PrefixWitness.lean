import PoincareConjecture.Definitions.Ch17.GlobalSurgery

set_option autoImplicit false

namespace PoincareConjecture

def GlobalSurgerySchedule.parameterPrefix {K : MetricSurgeryConstants}
    (S : GlobalSurgerySchedule K) (i : Nat) (hi : 0 < i) :
    SurgeryParameterPrefix K where
  setup := S.setup
  i := i
  i_pos := hi
  r j := S.r j.val
  kappa j := S.kappa j.val
  Delta j := S.Delta j.val
  r_pos j := S.r_pos j.val
  kappa_pos j := S.kappa_pos j.val
  Delta_pos j := S.Delta_pos j.val
  r_antitone := fun {_ _} h => S.r_antitone h
  kappa_antitone := fun {_ _} h => S.kappa_antitone h
  Delta_antitone := fun {_ _} h => S.Delta_antitone h
  r_zero := S.r_zero
  r_le_epsilon j := S.r_le_epsilon j.val
  Delta_le_setup j := S.Delta_le j.val

theorem globalSurgeryPrefixWitness_of_schedule {K : MetricSurgeryConstants}
    (S : GlobalSurgerySchedule K) (i : Nat) (hi : 0 < i) :
    Nonempty (GlobalSurgeryPrefixWitness K S i) := by
  exact ⟨{
    param_prefix := S.parameterPrefix i hi
    prefix_index := rfl
    setup_eq := rfl
    prefix_agrees := ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩ }⟩

end PoincareConjecture
