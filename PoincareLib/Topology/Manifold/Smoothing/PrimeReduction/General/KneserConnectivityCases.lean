import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-!
# The five connectivity cases on the three-region sphere cut

Kneser's sphere replacement argument (1929, p. 254) distinguishes the five
partitions of the three regions adjacent to the cut sphere.  This file records
the finite combinatorial boundary of that argument.  It deliberately does not
claim any 3-manifold or `L3` conclusion: those are supplied by the geometric
carrier and product-handle producers that consume this case split.
-/

set_option autoImplicit false

namespace PoincareMT.M76

/-- Every equivalence relation on the three labels has exactly one of the five
partitions used in Kneser's sphere surgery: all together, one of the three
two-plus-one partitions, or all distinct. -/
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

end PoincareMT.M76
