import PoincareConjecture.Statements.M52GlobalFlow
import PoincareConjecture.Proofs.M52.Assembly

set_option autoImplicit false

universe u

namespace PoincareConjecture

theorem repairedGlobalFlow : RepairedGlobalFlowTheory.{u} := by
  refine ⟨?_⟩
  intro B28 E34 U35 S36 P44 L15 U43 S45 N46 C47 E48 P48 V49 F50 G51 epsilon_bound hpositive
  obtain ⟨K, schedule, hepsilon, extend, start⟩ :=
    G51.uniform_schedule B28 E34 U35 S36 P44 L15 U43 S45 N46 C47 E48 P48 V49 F50
      epsilon_bound hpositive
  refine ⟨K, schedule, hepsilon, extend, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ _ N hprojective delta hantitone hpositive hcutoff
  obtain ⟨G, hK, hschedule, hdelta⟩ :=
    start N hprojective delta hantitone hpositive hcutoff
  obtain ⟨R, hR⟩ := m52GlobalFlowDataFromSchedule G
  refine ⟨R, ?_, ?_, ?_⟩
  · rw [hR]
    exact hK
  · rw [hR]
    exact hschedule
  · rw [hR]
    exact hdelta

end PoincareConjecture
