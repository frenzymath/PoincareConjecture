import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

set_option autoImplicit false

namespace PoincareConjecture.M76

theorem fin3_equivalence_partition_cases
    (r : Fin 3 → Fin 3 → Prop)
    (hrefl : ∀ i, r i i)
    (hsymm : ∀ ⦃i j⦄, r i j → r j i)
    (htrans : ∀ ⦃i j k⦄, r i j → r j k → r i k) :
    (∀ i j, r i j) ∨
      (r 0 1 ∧ ¬ r 0 2 ∧ ¬ r 1 2) ∨
      (r 0 2 ∧ ¬ r 0 1 ∧ ¬ r 1 2) ∨
      (r 1 2 ∧ ¬ r 0 1 ∧ ¬ r 0 2) ∨
      (¬ r 0 1 ∧ ¬ r 0 2 ∧ ¬ r 1 2) := by
  by_cases h01 : r 0 1
  · by_cases h02 : r 0 2
    · left
      intro i j
      fin_cases i <;> fin_cases j
      · exact hrefl 0
      · exact h01
      · exact h02
      · exact hsymm h01
      · exact hrefl 1
      · exact htrans (hsymm h01) h02
      · exact hsymm h02
      · exact htrans (hsymm h02) h01
      · exact hrefl 2
    · right
      left
      refine ⟨h01, h02, ?_⟩
      intro h12
      exact h02 (htrans h01 h12)
  · by_cases h02 : r 0 2
    · right
      right
      left
      refine ⟨h02, h01, ?_⟩
      intro h12
      exact h01 (htrans h02 (hsymm h12))
    · by_cases h12 : r 1 2
      · right
        right
        right
        left
        exact ⟨h12, h01, h02⟩
      · right
        right
        right
        right
        exact ⟨h01, h02, h12⟩

end PoincareConjecture.M76
