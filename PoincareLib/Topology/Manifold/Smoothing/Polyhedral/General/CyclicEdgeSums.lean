import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Splitting cyclic edge sums

Concatenating two nonempty vertex strings gives two smaller
cycles whose added edges cancel whenever their weights sum
to zero. See Erickson, Simple Polygons, pp. 8--9 and M76
derivation 103.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fin

variable {E G : Type*} [AddCommMonoid G] {m n : ℕ}

/-- Sum an edge weight around a finite cyclic vertex string,
including the closing edge. See M76 derivation 103. -/
def cyclicEdgeSum (w : E → E → G) (v : Fin n → E) : G :=
  ∑ i, w (v i) (v (finRotate n i))

private theorem rotate_castSucc {n : ℕ} (i : Fin n) :
    finRotate (n + 1) i.castSucc = i.succ := finRotate_of_lt i.isLt

/-- A cycle with an appended last vertex consists of the forward
path sum and the final closing edge. See M76 derivation 103. -/
theorem cyclicEdgeSum_snoc (w : E → E → G) (u : Fin (n + 1) → E) (z : E) :
    cyclicEdgeSum w (snoc u z) =
      (∑ i, w (u i) (snoc (α := fun _ => E) u z i.succ)) + w z (u 0) := by
  unfold cyclicEdgeSum
  rw [sum_univ_castSucc]
  simp only [rotate_castSucc, snoc_castSucc, finRotate_last, snoc_last, snoc_apply_zero]

/-- The successor of a vertex in the first string follows that
string or reaches the first vertex of the second string.
See M76 derivation 103. -/
theorem append_finRotate_castAdd (u : Fin (m + 1) → E) (v : Fin (n + 1) → E)
    (i : Fin (m + 1)) :
    append u v (finRotate ((m + 1) + (n + 1)) (i.castAdd (n + 1))) =
      snoc (α := fun _ => E) u (v 0) i.succ := by
  have hrot (j : Fin (m + 1)) :
      finRotate ((m + 1) + (n + 1)) (j.castAdd (n + 1)) =
        ⟨j.val + 1, by omega⟩ :=
    finRotate_of_lt (n := (m + 1) + n) (show j.val < (m + 1) + n by omega)
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [hrot]
    change append u v (Fin.natAdd (m + 1) 0) =
      snoc (α := fun _ => E) u (v 0) (Fin.last (m + 1))
    rw [append_right, snoc_last]
  · rw [hrot]
    change append u v (j.succ.castAdd (n + 1)) =
      snoc (α := fun _ => E) u (v 0) j.succ.castSucc
    rw [append_left, snoc_castSucc]

/-- The successor of a vertex in the second string follows that
string or closes the cycle at the first vertex of the first string.
See M76 derivation 103. -/
theorem append_finRotate_natAdd (u : Fin (m + 1) → E) (v : Fin (n + 1) → E)
    (i : Fin (n + 1)) :
    append u v (finRotate ((m + 1) + (n + 1)) (Fin.natAdd (m + 1) i)) =
      snoc (α := fun _ => E) v (u 0) i.succ := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.natAdd_last]
    change append u v (finRotate (((m + 1) + n) + 1) (Fin.last ((m + 1) + n))) =
      snoc (α := fun _ => E) v (u 0) (Fin.last (n + 1))
    rw [finRotate_last]
    change append u v ((0 : Fin (m + 1)).castAdd (n + 1)) =
      snoc (α := fun _ => E) v (u 0) (Fin.last (n + 1))
    rw [append_left, snoc_last]
  · have hrot : finRotate ((m + 1) + (n + 1)) (Fin.natAdd (m + 1) j.castSucc) =
        Fin.natAdd (m + 1) j.succ :=
      finRotate_of_lt (Nat.add_lt_add_left j.isLt (m + 1))
    rw [hrot]
    change append u v (Fin.natAdd (m + 1) j.succ) =
      snoc (α := fun _ => E) v (u 0) j.succ.castSucc
    rw [append_right, snoc_castSucc]

/-- The cyclic sum of concatenated nonempty strings splits into
the two forward path sums with their original joining edges.
See Erickson pp. 8--9 and M76 derivation 103. -/
theorem cyclicEdgeSum_append (w : E → E → G)
    (u : Fin (m + 1) → E) (v : Fin (n + 1) → E) :
    cyclicEdgeSum w (append u v) =
      (∑ i, w (u i) (snoc (α := fun _ => E) u (v 0) i.succ)) +
        ∑ i, w (v i) (snoc (α := fun _ => E) v (u 0) i.succ) := by
  unfold cyclicEdgeSum
  rw [sum_univ_add]
  simp only [append_left, append_right, append_finRotate_castAdd, append_finRotate_natAdd]

/-- Adding oppositely cancelling diagonal edges splits one cyclic
edge sum into two cyclic edge sums. Only cancellation of the two
specified edges is required. See Erickson pp. 8--9 and derivation 103. -/
theorem cyclicEdgeSum_append_split (w : E → E → G)
    (u : Fin (m + 1) → E) (v : Fin (n + 1) → E)
    (hcancel : w (u 0) (v 0) + w (v 0) (u 0) = 0) :
    cyclicEdgeSum w (append u v) =
      cyclicEdgeSum w (snoc u (v 0)) + cyclicEdgeSum w (snoc v (u 0)) := by
  rw [cyclicEdgeSum_append, cyclicEdgeSum_snoc, cyclicEdgeSum_snoc,
    add_add_add_comm, add_comm (w (v 0) (u 0)), hcancel, add_zero]

end Fin
