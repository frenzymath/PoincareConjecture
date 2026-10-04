import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic

/-! Adapted from Mapher `PoincareMT/Proofs/M54/Mathlib/GridProduct.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`; see `references/ricci-flow/mapher/group-effects.md`. -/

/-!
# Ordered products around a rectangular grid

The algebraic rectangle argument in Hatcher Theorem 1.20 (pp. 45-46),
used for Morgan--Tian Proposition 15.3. If each cell commutes, the outer
rectangle commutes. Products retain their order; a monoid suffices.
-/

set_option autoImplicit false

namespace List

variable {M : Type*} [Monoid M]

/-- Group adjacent pairs in an ordered finite product, as required by
dyadic refinement in the proof of Hatcher Theorem 1.20 (pp. 43-46). -/
theorem prod_range_pairs (f : ℕ → M) (n : ℕ) :
    ((range (2 * n)).map f).prod =
      ((range n).map (fun i => f (2 * i) * f (2 * i + 1))).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
      prod_range_succ, prod_range_succ, ih, prod_range_succ, mul_assoc]

/-- Commuting cells imply a commuting horizontal strip. This is the
one-row case of Hatcher's rectangle argument (Theorem 1.20, pp. 45-46). -/
theorem prod_range_strip (h v : ℕ → ℕ → M) (n j : ℕ)
    (hc : ∀ i < n, h i j * v (i + 1) j = v i j * h i (j + 1)) :
    ((range n).map (fun i => h i j)).prod * v n j =
      v 0 j * ((range n).map (fun i => h i (j + 1))).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, mul_assoc, hc n (by omega), ← mul_assoc,
      ih (fun i hi => hc i (by omega)), mul_assoc, ← prod_range_succ]

/-- Commuting cells imply a commuting outer rectangle, with all boundary
products in their original order (Hatcher Theorem 1.20, pp. 45-46). -/
theorem prod_range_grid (h v : ℕ → ℕ → M) (n m : ℕ)
    (hc : ∀ i < n, ∀ j < m,
      h i j * v (i + 1) j = v i j * h i (j + 1)) :
    ((range n).map (fun i => h i 0)).prod *
        ((range m).map (fun j => v n j)).prod =
      ((range m).map (fun j => v 0 j)).prod *
        ((range n).map (fun i => h i m)).prod := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prod_range_succ, ← mul_assoc,
      ih (fun i hi j hj => hc i hi j (by omega)), mul_assoc,
      prod_range_strip h v n m (fun i hi => hc i hi m (by omega)),
      ← mul_assoc, ← prod_range_succ]

end List
