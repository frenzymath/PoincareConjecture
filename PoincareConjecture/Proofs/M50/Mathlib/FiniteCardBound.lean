import Mathlib.Data.Set.Finite.Basic








set_option autoImplicit false

namespace Set



theorem finite_of_forall_finset_card_le {α : Type*} (s : Set α) (n : ℕ)
    (bound : ∀ A : Finset α, (↑A : Set α) ⊆ s → A.card ≤ n) :
    s.Finite := by
  classical
  by_contra hinfinite
  obtain ⟨A, hA, hcard⟩ := Set.Infinite.exists_subset_card_eq hinfinite (n + 1)
  have hle : n + 1 ≤ n := by simpa only [hcard] using bound A hA
  exact Nat.not_succ_le_self n hle

end Set
