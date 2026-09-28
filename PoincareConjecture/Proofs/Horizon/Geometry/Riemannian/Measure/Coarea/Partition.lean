import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.Algebra.Support

set_option autoImplicit false

open Set
open scoped BigOperators

namespace Poincare.Coarea

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]

theorem exists_continuous_decomposition_of_finite_cover
    {ι : Type*} [Fintype ι] (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    {h : X → ℝ} (hh : Continuous h) (hc : HasCompactSupport h)
    (hcover : tsupport h ⊆ ⋃ i, U i) :
    ∃ H : ι → X → ℝ,
      (∀ i, Continuous (H i)) ∧ (∀ i, HasCompactSupport (H i)) ∧
      (∀ i, tsupport (H i) ⊆ U i ∩ tsupport h) ∧
      ∀ x, ∑ i, H i x = h x := by
  obtain ⟨ρ, hρ, _⟩ := PartitionOfUnity.exists_isSubordinate_of_locallyFinite_t2space
    hc.isCompact U hU (locallyFinite_of_finite U) hcover
  refine ⟨fun i x => ρ i x * h x, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (ρ i).continuous.mul hh
  · intro i
    exact hc.mul_left
  · intro i
    exact subset_inter (tsupport_mul_subset_left.trans (hρ i)) tsupport_mul_subset_right
  · intro x
    rw [← Finset.sum_mul]
    by_cases hx : x ∈ tsupport h
    · have hsum : ∑ i, ρ i x = 1 := by
        simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hx
      rw [hsum, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

theorem exists_finite_continuous_decomposition
    {ι : Type*} (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    {h : X → ℝ} (hh : Continuous h) (hc : HasCompactSupport h)
    (hcover : tsupport h ⊆ ⋃ i, U i) :
    ∃ s : Finset ι, ∃ H : s → X → ℝ,
      (∀ i, Continuous (H i)) ∧ (∀ i, HasCompactSupport (H i)) ∧
      (∀ i, tsupport (H i) ⊆ U i ∩ tsupport h) ∧
      ∀ x, ∑ i, H i x = h x := by
  classical
  obtain ⟨s, hs⟩ := hc.isCompact.elim_finite_subcover U hU hcover
  have hscover : tsupport h ⊆ ⋃ i : s, U i := by
    simpa only [iUnion_subtype] using hs
  obtain ⟨H, hH⟩ := exists_continuous_decomposition_of_finite_cover
    (fun i : s => U i) (fun i => hU i) hh hc hscover
  exact ⟨s, H, hH⟩

end Poincare.Coarea
