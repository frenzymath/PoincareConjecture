import Mathlib.Data.Set.Finite.Basic

/-!
# Finiteness from bounded finite subsets

The set-theoretic step in Morgan--Tian, Lemma 17.12, pp. 410-411.
Adapted from `PoincareMT/Proofs/M50/Mathlib/FiniteCardBound.lean` at
Mapher revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.
-/

set_option autoImplicit false

namespace Set

/-- A common cardinal bound on finite subsets forces finiteness. -/
theorem finite_of_forall_finset_card_le {α : Type*} (s : Set α) (n : ℕ)
    (bound : ∀ A : Finset α, (↑A : Set α) ⊆ s → A.card ≤ n) :
    s.Finite := by
  classical
  by_contra hinfinite
  obtain ⟨A, hA, hcard⟩ := Set.Infinite.exists_subset_card_eq hinfinite (n + 1)
  have hle : n + 1 ≤ n := by simpa only [hcard] using bound A hA
  exact Nat.not_succ_le_self n hle

end Set
