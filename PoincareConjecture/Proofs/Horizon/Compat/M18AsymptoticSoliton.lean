import PoincareConjecture.Definitions.M18AsymptoticSoliton

set_option autoImplicit false

namespace PoincareConjecture

theorem ancientM18TimeWindow_mono {j k : ℕ} (h : j ≤ k) :
    ancientM18TimeWindow j ⊆ ancientM18TimeWindow k := by
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hjk : (j : ℝ) + 1 ≤ (k : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ h
  refine Set.Icc_subset_Icc (by linarith) ?_
  exact neg_le_neg (inv_anti₀ hj hjk)

theorem ancientM18TimeWindow_subset (j : ℕ) : ancientM18TimeWindow j ⊆ Set.Iio 0 := by
  intro t ht
  have hpos : (0 : ℝ) < ((j : ℝ) + 1)⁻¹ := by positivity
  exact lt_of_le_of_lt ht.2 (by linarith)

theorem ancientM18TimeWindow_increasing (j : ℕ) :
    ancientM18TimeWindow j ⊆ ancientM18TimeWindow (j + 1) :=
  ancientM18TimeWindow_mono (Nat.le_succ j)

theorem ancientM18TimeWindow_base (j : ℕ) : (-1 : ℝ) ∈ ancientM18TimeWindow j := by
  have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)]
  refine ⟨by linarith, ?_⟩
  have : ((j : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hj
  linarith

theorem ancientM18TimeWindow_covers : ⋃ j, ancientM18TimeWindow j = Set.Iio 0 := by
  ext t
  constructor
  · intro ht
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp ht
    have hpos : (0 : ℝ) < ((j : ℝ) + 1)⁻¹ := by positivity
    exact lt_of_le_of_lt hj.2 (by linarith)
  · intro ht
    have hpos : (0 : ℝ) < -t := neg_pos.mpr ht
    obtain ⟨j, hj⟩ := exists_nat_ge (max (-t) (-t)⁻¹)
    refine Set.mem_iUnion.mpr ⟨j, ?_, ?_⟩
    · have := le_max_left (-t) (-t)⁻¹
      linarith
    · have h1 : (-t)⁻¹ ≤ (j : ℝ) + 1 := by linarith [le_max_right (-t) (-t)⁻¹]
      have h2 : ((j : ℝ) + 1)⁻¹ ≤ -t := (inv_le_comm₀ (by positivity) hpos).mpr h1
      linarith

end PoincareConjecture
