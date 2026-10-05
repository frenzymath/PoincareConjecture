import PoincareLib.Geometry.RicciFlow.Surgery.Global.Certificate

/-! Restrict a final numerical schedule without assuming any flow extension.
M51 may use this helper after constructing its global schedule. It does not
describe the intermediate, subsequently tightened induction prefixes. -/

set_option autoImplicit false

namespace PoincareMT

/-- The finite sequence is the literal restriction of the chosen schedule. -/
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

/-- Every positive finite restriction has a witness, independently of any
flow, observation horizon, noncollapsing result or continuation theorem.
Source: the sequence restrictions in Morgan--Tian Definition 15.7, p. 360. -/
theorem globalSurgeryPrefixWitness_of_schedule {K : MetricSurgeryConstants}
    (S : GlobalSurgerySchedule K) (i : Nat) (hi : 0 < i) :
    Nonempty (GlobalSurgeryPrefixWitness K S i) := by
  exact ⟨{
    param_prefix := S.parameterPrefix i hi
    prefix_index := rfl
    setup_eq := rfl
    prefix_agrees := ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩ }⟩

end PoincareMT
