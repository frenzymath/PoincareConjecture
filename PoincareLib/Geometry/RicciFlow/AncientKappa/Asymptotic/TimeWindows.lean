import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Compact time windows for an ancient limit

The definition is unchanged from Mapher's M18 definition file at revision
49331b7d7ecad38f53e4300c3b35d6a84b2cc648. These windows exhaust the open
ancient interval while retaining the based time -1.
-/

set_option autoImplicit false

namespace PoincareMT

def ancientM18TimeWindow (j : ℕ) : Set ℝ :=
  Set.Icc (-((j : ℝ) + 1)) (-((j : ℝ) + 1)⁻¹)

theorem ancientM18TimeWindow_subset (j : ℕ) : ancientM18TimeWindow j ⊆ Set.Iio 0 := by
  intro t ht
  exact lt_of_le_of_lt ht.2 (neg_neg_of_pos (inv_pos.mpr (by positivity)))

theorem ancientM18TimeWindow_base (j : ℕ) : (-1 : ℝ) ∈ ancientM18TimeWindow j := by
  constructor
  · have := Nat.cast_nonneg (α := ℝ) j
    linarith
  · exact neg_le_neg ((inv_le_one₀ (by positivity : 0 < (j : ℝ) + 1)).2
      (le_add_of_nonneg_left (Nat.cast_nonneg j)))

theorem ancientM18TimeWindow_mono : Monotone ancientM18TimeWindow := by
  intro i j hij t ht
  have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
  refine ⟨?_, ?_⟩
  · exact le_trans (by linarith) ht.1
  · apply le_trans ht.2
    apply neg_le_neg
    exact (inv_le_inv₀ (by positivity : 0 < (j : ℝ) + 1)
      (by positivity : 0 < (i : ℝ) + 1)).2 (by linarith)

theorem ancientM18TimeWindow_increasing (j : ℕ) :
    ancientM18TimeWindow j ⊆ ancientM18TimeWindow (j + 1) :=
  ancientM18TimeWindow_mono (Nat.le_succ j)

theorem ancientM18TimeWindow_covers : ⋃ j, ancientM18TimeWindow j = Set.Iio 0 := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset ancientM18TimeWindow_subset
  · intro t ht
    have ht' : 0 < -t := neg_pos.mpr ht
    obtain ⟨j, hj⟩ := exists_nat_gt (max (-t) (-t)⁻¹)
    have hleft : -t ≤ (j : ℝ) + 1 := by
      have := le_max_left (-t) (-t)⁻¹
      linarith
    have hright : (-t)⁻¹ ≤ (j : ℝ) + 1 := by
      have := le_max_right (-t) (-t)⁻¹
      linarith
    have hinv : ((j : ℝ) + 1)⁻¹ ≤ -t := by
      have h := (inv_le_inv₀ (by positivity : 0 < (j : ℝ) + 1)
        (inv_pos.mpr ht')).2 hright
      simpa only [inv_inv] using h
    exact Set.mem_iUnion.mpr ⟨j, ⟨by linarith, by linarith⟩⟩

theorem isCompact_ancientM18TimeWindow (j : ℕ) : IsCompact (ancientM18TimeWindow j) :=
  isCompact_Icc

end PoincareMT
