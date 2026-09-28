import PoincareConjecture.Definitions.Ch16.ControlledSurgery









set_option autoImplicit false

namespace PoincareConjecture

theorem exists_surgeryEpochEntry {t : ℝ} (ht : 0 ≤ t) :
    ∃ j : ℕ, t ∈ surgeryEpochEntry j := by
  by_cases hsmall : t < 1 / 32
  · exact ⟨0, by simpa [surgeryEpochEntry, surgeryEpochStart] using And.intro ht hsmall⟩
  · have hlarge : 1 ≤ 32 * t := by linarith
    obtain ⟨j, hlo, hhi⟩ := exists_nat_pow_near hlarge (by norm_num : (1 : ℝ) < 2)
    refine ⟨j + 1, ?_⟩
    simp only [surgeryEpochEntry, Nat.add_one_ne_zero, if_false,
      Nat.add_sub_cancel, surgeryEpochStart, Set.mem_Ico]
    constructor <;> linarith

end PoincareConjecture
