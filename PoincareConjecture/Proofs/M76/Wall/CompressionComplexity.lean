import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Group.Nat












set_option autoImplicit false

namespace PoincareConjecture.M76.Wall



def compressionComplexity (genera : List ℕ) : ℕ :=
  (genera.map fun g => 2 * g - 1).sum


theorem compressionComplexity_nil : compressionComplexity [] = 0 := rfl



theorem compressionComplexity_cons (g : ℕ) (genera : List ℕ) :
    compressionComplexity (g :: genera) = 2 * g - 1 + compressionComplexity genera :=
  rfl



theorem compressionComplexity_eq_zero_iff (genera : List ℕ) :
    compressionComplexity genera = 0 ↔ ∀ g ∈ genera, g = 0 := by
  induction genera with
  | nil => simp [compressionComplexity]
  | cons g genera ih =>
    rw [compressionComplexity_cons, Nat.add_eq_zero_iff, ih]
    simp only [List.mem_cons, forall_eq_or_imp]
    have hweight : 2 * g - 1 = 0 ↔ g = 0 := by omega
    rw [hweight]



theorem compressionComplexity_nonseparating (g : ℕ) (hg : 0 < g)
    (genera : List ℕ) :
    compressionComplexity ((g - 1) :: genera) <
      compressionComplexity (g :: genera) := by
  simp only [compressionComplexity_cons]
  omega




theorem compressionComplexity_separating (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (genera : List ℕ) :
    compressionComplexity (a :: b :: genera) <
      compressionComplexity ((a + b) :: genera) := by
  simp only [compressionComplexity_cons]
  omega



theorem compressionComplexity_sublist {kept genera : List ℕ} (h : kept.Sublist genera) :
    compressionComplexity kept ≤ compressionComplexity genera := by
  exact (h.map (fun g => 2 * g - 1)).sum_le_sum (fun _ _ => Nat.zero_le _)



theorem compressionComplexity_nonseparating_sublist (g : ℕ) (hg : 0 < g)
    (genera kept : List ℕ) (hkept : kept.Sublist ((g - 1) :: genera)) :
    compressionComplexity kept < compressionComplexity (g :: genera) :=
  lt_of_le_of_lt (compressionComplexity_sublist hkept)
    (compressionComplexity_nonseparating g hg genera)



theorem compressionComplexity_separating_sublist (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (genera kept : List ℕ) (hkept : kept.Sublist (a :: b :: genera)) :
    compressionComplexity kept < compressionComplexity ((a + b) :: genera) :=
  lt_of_le_of_lt (compressionComplexity_sublist hkept)
    (compressionComplexity_separating a b ha hb genera)

end PoincareConjecture.M76.Wall
