import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Windows




set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture.AncientRescalingSequence

def shiftedCompactnessWindow (j : ℕ) : Set ℝ :=
  Ioo (compactnessLower j + 1) (compactnessUpper j + 1)

theorem shiftedCompactnessWindow_mono : Monotone shiftedCompactnessWindow := by
  intro i j hij
  apply Ioo_subset_Ioo
  · dsimp [compactnessLower]
    exact_mod_cast (show -((j : ℤ) + 2) + 1 ≤ -((i : ℤ) + 2) + 1 by omega)
  · have hcast : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hij
    have hi := (inv_le_inv₀ (by positivity : (0 : ℝ) < (j : ℝ) + 2)
      (by positivity : (0 : ℝ) < (i : ℝ) + 2)).2
      (by linarith)
    dsimp [compactnessUpper]
    linarith

theorem shiftedCompactnessWindow_subset (j : ℕ) : shiftedCompactnessWindow j ⊆ Iio 1 := by
  intro t ht
  exact ht.2.trans (by linarith [compactnessUpper_neg j])

theorem exists_mem_shiftedCompactnessWindow (t : ℝ) (ht : t < 1) :
    ∃ j, t ∈ shiftedCompactnessWindow j := by
  obtain ⟨j, hj⟩ := exists_nat_gt (max (-t) (1 / (1 - t)))
  have hjt : -t < (j : ℝ) := (le_max_left _ _).trans_lt hj
  have hjr : 1 / (1 - t) < (j : ℝ) := (le_max_right _ _).trans_lt hj
  have hprod : 1 < (j : ℝ) * (1 - t) := (div_lt_iff₀ (by linarith)).mp hjr
  refine ⟨j, ?_, ?_⟩
  · change -((j : ℝ) + 2) + 1 < t
    linarith
  · have hinv : ((j : ℝ) + 2)⁻¹ < 1 - t :=
      (by
        rw [inv_eq_one_div]
        exact (div_lt_iff₀ (by positivity : (0 : ℝ) < (j : ℝ) + 2)).2 (by nlinarith))
    change t < -((j : ℝ) + 2)⁻¹ + 1
    linarith

theorem shiftedCompactnessWindow_cover : (⋃ j, shiftedCompactnessWindow j) = Iio 1 := by
  apply Subset.antisymm
  · exact iUnion_subset shiftedCompactnessWindow_subset
  · intro t ht
    exact mem_iUnion.mpr (exists_mem_shiftedCompactnessWindow t ht)

theorem exists_compact_subset_shiftedCompactnessWindow {K : Set ℝ} (hK : IsCompact K)
    (hKU : K ⊆ Iio 1) : ∃ j, K ⊆ shiftedCompactnessWindow j := by
  apply hK.elim_directed_cover shiftedCompactnessWindow (fun _ => isOpen_Ioo)
  · simpa only [shiftedCompactnessWindow_cover] using hKU
  · exact shiftedCompactnessWindow_mono.directed_le

end PoincareConjecture.AncientRescalingSequence
