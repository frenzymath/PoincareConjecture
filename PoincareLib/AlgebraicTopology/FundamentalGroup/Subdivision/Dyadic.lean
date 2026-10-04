import Mathlib.Topology.UnitInterval
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic

/-! Adapted from Mapher `PoincareMT/Proofs/M54/Mathlib/DyadicSubdivision.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`; see `references/ricci-flow/mapher/group-effects.md`. -/

/-!
# Nested subdivisions of paths and homotopies

The compactness subdivision in Hatcher Theorem 1.20 (pp. 43-46), used for
Morgan--Tian Proposition 15.3 (pp. 357-358). Dyadic meshes provide common
refinements while preserving the order of noncommutative path products.
-/

set_option autoImplicit false

open Set Metric
open scoped unitInterval

namespace unitInterval

/-- The clipped dyadic mesh, for the rectangle proof of van Kampen in
Hatcher Theorem 1.20 (pp. 43-46). -/
noncomputable def dyadicPoint (n k : ℕ) : unitInterval :=
  projIcc 0 1 zero_le_one ((k : ℝ) * (1 / 2 : ℝ) ^ n)

private theorem dyadic_scale (n : ℕ) :
    ((2 ^ n : ℕ) : ℝ) * (1 / 2 : ℝ) ^ n = 1 := by
  push_cast
  rw [← mul_pow]
  norm_num

/-- Before the last mesh point, clipping has no effect (the mesh for
Hatcher Theorem 1.20, pp. 43-46). -/
theorem dyadicPoint_coe (n k : ℕ) (hk : k ≤ 2 ^ n) :
    (dyadicPoint n k : ℝ) = (k : ℝ) * (1 / 2 : ℝ) ^ n := by
  have hlo : 0 ≤ (k : ℝ) * (1 / 2 : ℝ) ^ n := by positivity
  have hhi : (k : ℝ) * (1 / 2 : ℝ) ^ n ≤ 1 := by
    calc
      _ ≤ ((2 ^ n : ℕ) : ℝ) * (1 / 2 : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (by positivity)
      _ = 1 := dyadic_scale n
  exact congrArg Subtype.val (projIcc_of_mem zero_le_one ⟨hlo, hhi⟩)

/-- The mesh starts at zero (Hatcher Theorem 1.20 construction,
pp. 43-46). -/
@[simp] theorem dyadicPoint_zero (n : ℕ) : dyadicPoint n 0 = 0 := by
  apply Subtype.ext
  rw [dyadicPoint_coe n 0 (Nat.zero_le _)]
  simp

/-- The last point of the mesh is one (Hatcher Theorem 1.20 construction,
pp. 43-46). -/
@[simp] theorem dyadicPoint_last (n : ℕ) : dyadicPoint n (2 ^ n) = 1 := by
  apply Subtype.ext
  rw [dyadicPoint_coe n (2 ^ n) le_rfl]
  exact dyadic_scale n

/-- Mesh points are monotone, including the clipped tail
(Hatcher Theorem 1.20 construction, pp. 43-46). -/
theorem dyadicPoint_mono (n : ℕ) : Monotone (dyadicPoint n) := by
  intro i j hij
  apply monotone_projIcc _
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (by positivity)

/-- Every second point of the refined mesh is an old mesh point
(Hatcher Theorem 1.20 construction, pp. 43-46). -/
@[simp] theorem dyadicPoint_even (n k : ℕ) :
    dyadicPoint (n + 1) (2 * k) = dyadicPoint n k := by
  unfold dyadicPoint
  congr 1
  push_cast
  rw [pow_succ]
  ring

/-- Each dyadic cell has diameter at most its mesh size
(Hatcher Theorem 1.20 construction, pp. 43-46). -/
theorem dyadicPoint_dist_le {n k : ℕ} (hk : k < 2 ^ n)
    {x : unitInterval} (hx : x ∈ Icc (dyadicPoint n k) (dyadicPoint n (k + 1))) :
    dist x (dyadicPoint n k) ≤ (1 / 2 : ℝ) ^ n := by
  have hlo : (dyadicPoint n k : ℝ) ≤ (x : ℝ) := hx.1
  rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hlo)]
  have hhi : (x : ℝ) ≤ (dyadicPoint n (k + 1) : ℝ) := hx.2
  rw [dyadicPoint_coe n k hk.le,
    dyadicPoint_coe n (k + 1) (by omega)] at *
  push_cast at hhi
  nlinarith

/-- Every open cover of the interval admits a subordinate dyadic mesh,
the compactness step in Hatcher Theorem 1.20 (pp. 43-46). -/
theorem exists_dyadic_subordinate {ι : Type*} (U : ι → Set unitInterval)
    (hU : ∀ i, IsOpen (U i)) (hcover : univ ⊆ ⋃ i, U i) :
    ∃ n : ℕ, ∀ k < 2 ^ n, ∃ i,
      Icc (dyadicPoint n k) (dyadicPoint n (k + 1)) ⊆ U i := by
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hU hcover
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨n, fun k hk => ?_⟩
  obtain ⟨i, hi⟩ := hball (dyadicPoint n k) (mem_univ _)
  exact ⟨i, fun x hx => hi (mem_ball.mpr ((dyadicPoint_dist_le hk hx).trans_lt hn))⟩

/-- Every open cover of a square admits a subordinate dyadic grid,
as in Hatcher's van Kampen homotopy argument (Theorem 1.20, pp. 45-46). -/
theorem exists_dyadic_square_subordinate {ι : Type*}
    (U : ι → Set (unitInterval × unitInterval))
    (hU : ∀ i, IsOpen (U i)) (hcover : univ ⊆ ⋃ i, U i) :
    ∃ n : ℕ, ∀ k < 2 ^ n, ∀ l < 2 ^ n, ∃ i,
      Icc (dyadicPoint n k) (dyadicPoint n (k + 1)) ×ˢ
        Icc (dyadicPoint n l) (dyadicPoint n (l + 1)) ⊆ U i := by
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hU hcover
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨n, fun k hk l hl => ?_⟩
  obtain ⟨i, hi⟩ := hball (dyadicPoint n k, dyadicPoint n l) (mem_univ _)
  refine ⟨i, fun x hx => hi (mem_ball.mpr ?_)⟩
  rw [Prod.dist_eq]
  exact (max_le (dyadicPoint_dist_le hk hx.1)
    (dyadicPoint_dist_le hl hx.2)).trans_lt hn

/-- A refined dyadic cell lies in the old cell with half its index
(Hatcher Theorem 1.20 construction, pp. 43-46). -/
theorem dyadic_cell_subset (n k : ℕ) :
    Icc (dyadicPoint (n + 1) k) (dyadicPoint (n + 1) (k + 1)) ⊆
      Icc (dyadicPoint n (k / 2)) (dyadicPoint n (k / 2 + 1)) := by
  rw [← dyadicPoint_even n (k / 2), ← dyadicPoint_even n (k / 2 + 1)]
  exact Icc_subset_Icc ((dyadicPoint_mono _ ) (by omega))
    ((dyadicPoint_mono _) (by omega))

end unitInterval
