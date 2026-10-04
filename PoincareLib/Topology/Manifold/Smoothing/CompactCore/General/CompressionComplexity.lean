import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Group.Nat

/-!
# The strict measure for protected surface compression

The positive-genus contribution is `2 * g - 1`, with natural subtraction
giving zero for a sphere. Unlike total genus, its sum decreases under
both types of essential compression. This is the arithmetic part of M76
derivation 318 and input Wall derivation `001_compression_complexity.md`,
on the route from Hatcher Corollary 3.3, p. 48, to Hamilton Lemma 2,
p. 64. No geometric compression or surface classification is asserted.
-/

set_option autoImplicit false

namespace PoincareMT.M76.Wall

/-- Sum of the positive-genus compression weights, retaining genus-zero
components. See Wall input derivation 001 and M76 derivation 318. -/
def compressionComplexity (genera : List ℕ) : ℕ :=
  (genera.map fun g => 2 * g - 1).sum

/-- The empty component list has measure zero. See Wall derivation 001. -/
theorem compressionComplexity_nil : compressionComplexity [] = 0 := rfl

/-- One component contributes its literal natural-number weight.
See Wall derivation 001. -/
theorem compressionComplexity_cons (g : ℕ) (genera : List ℕ) :
    compressionComplexity (g :: genera) = 2 * g - 1 + compressionComplexity genera :=
  rfl

/-- The measure vanishes exactly when every retained component has genus
zero, including the empty-list case. See Wall derivation 001. -/
theorem compressionComplexity_eq_zero_iff (genera : List ℕ) :
    compressionComplexity genera = 0 ↔ ∀ g ∈ genera, g = 0 := by
  induction genera with
  | nil => simp [compressionComplexity]
  | cons g genera ih =>
    rw [compressionComplexity_cons, Nat.add_eq_zero_iff, ih]
    simp only [List.mem_cons, forall_eq_or_imp]
    have hweight : 2 * g - 1 = 0 ↔ g = 0 := by omega
    rw [hweight]

/-- Nonseparating compression lowers the measure even when a torus becomes
a sphere. See M76 derivation 318 and Wall input derivation 001. -/
theorem compressionComplexity_nonseparating (g : ℕ) (hg : 0 < g)
    (genera : List ℕ) :
    compressionComplexity ((g - 1) :: genera) <
      compressionComplexity (g :: genera) := by
  simp only [compressionComplexity_cons]
  omega

/-- Essential separating compression splits into two positive genera and
strictly lowers the measure. Both positivity assumptions are required.
See M76 derivation 318 and Wall input derivation 001. -/
theorem compressionComplexity_separating (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (genera : List ℕ) :
    compressionComplexity (a :: b :: genera) <
      compressionComplexity ((a + b) :: genera) := by
  simp only [compressionComplexity_cons]
  omega

/-- Discarding unprotected connected components cannot increase the
compression measure. See M76 derivation 318 and Wall input derivation 001. -/
theorem compressionComplexity_sublist {kept genera : List ℕ} (h : kept.Sublist genera) :
    compressionComplexity kept ≤ compressionComplexity genera := by
  exact (h.map (fun g => 2 * g - 1)).sum_le_sum (fun _ _ => Nat.zero_le _)

/-- Discarding components after nonseparating compression preserves its
strict decrease. See M76 derivation 318 and Wall input derivation 001. -/
theorem compressionComplexity_nonseparating_sublist (g : ℕ) (hg : 0 < g)
    (genera kept : List ℕ) (hkept : kept.Sublist ((g - 1) :: genera)) :
    compressionComplexity kept < compressionComplexity (g :: genera) :=
  lt_of_le_of_lt (compressionComplexity_sublist hkept)
    (compressionComplexity_nonseparating g hg genera)

/-- Discarding components after separating compression preserves its
strict decrease. See M76 derivation 318 and Wall input derivation 001. -/
theorem compressionComplexity_separating_sublist (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (genera kept : List ℕ) (hkept : kept.Sublist (a :: b :: genera)) :
    compressionComplexity kept < compressionComplexity ((a + b) :: genera) :=
  lt_of_le_of_lt (compressionComplexity_sublist hkept)
    (compressionComplexity_separating a b ha hb genera)

end PoincareMT.M76.Wall
