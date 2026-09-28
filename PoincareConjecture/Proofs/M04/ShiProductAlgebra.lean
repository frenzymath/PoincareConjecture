import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

set_option autoImplicit false

open scoped BigOperators

namespace PoincareConjecture.M04

theorem finset_bilinear_sum_subset_le
    {α β : Type*} (s S : Finset α) (t T : Finset β)
    (f : α → ℝ) (g : β → ℝ)
    (hs : s ⊆ S) (ht : t ⊆ T)
    (hf : ∀ i ∈ S, 0 ≤ f i) (hg : ∀ j ∈ T, 0 ≤ g j) :
    (∑ i ∈ s, ∑ j ∈ t, f i * g j) ≤
      (∑ i ∈ S, f i) * (∑ j ∈ T, g j) := by
  have hfs : (∑ i ∈ s, f i) ≤ ∑ i ∈ S, f i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hs
    intro i hi hnot
    exact hf i (by exact hi)
  have hgt : (∑ j ∈ t, g j) ≤ ∑ j ∈ T, g j := by
    apply Finset.sum_le_sum_of_subset_of_nonneg ht
    intro j hj hnot
    exact hg j (by exact hj)
  have hfs_nonneg : 0 ≤ ∑ i ∈ s, f i := by
    exact Finset.sum_nonneg fun i hi => hf i (hs hi)
  have hST_nonneg : 0 ≤ ∑ i ∈ S, f i := by
    exact Finset.sum_nonneg fun i hi => hf i hi
  have hgt_nonneg : 0 ≤ ∑ j ∈ t, g j := by
    exact Finset.sum_nonneg fun j hj => hg j (ht hj)
  have hmul := mul_le_mul hfs hgt hgt_nonneg hST_nonneg
  have hbil_s :
      (∑ i ∈ s, ∑ j ∈ t, f i * g j) =
        (∑ i ∈ s, f i) * (∑ j ∈ t, g j) := by
    calc
      _ = ∑ i ∈ s, f i * (∑ j ∈ t, g j) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
      _ = _ := by rw [Finset.sum_mul]
  rw [hbil_s]
  exact hmul

end PoincareConjecture.M04
