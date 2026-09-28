import PoincareConjecture.Proofs.M76.Mathlib.SimplexCoreRegions

set_option autoImplicit false

open Set

namespace StdSimplexCore

variable {ι : Type*} [Fintype ι]

theorem face_threshold_bound (s : Finset ι) {η : ℝ} (hη : 0 ≤ η)
    (hbound : (Fintype.card ι : ℝ) * η < 1) : (Fintype.card s : ℝ) * η < 1 := by
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_right ?_ hη) hbound
  rw [Fintype.card_coe]
  exact_mod_cast (show s.card ≤ Fintype.card ι from Finset.card_le_univ s)

variable [DecidableEq ι]

theorem faceRegion_base_mem_intrinsicFrontier (s : Finset ι) (hs : s.Nonempty)
    {η : ℝ} (hη : 0 ≤ η) (hbound : (Fintype.card ι : ℝ) * η < 1)
    (q : faceRegion s η) {i : ι} (hi : i ∈ s) (he : q.val i = η) :
    (((faceRegionProductHomeomorph s hη hbound).symm q).1 : s → ℝ) ∈
      intrinsicFrontier ℝ (stdSimplexCore s η) := by
  have : Nonempty s := by
    obtain ⟨j, hj⟩ := hs
    exact ⟨⟨j, hj⟩⟩
  apply (mem_intrinsicFrontier_stdSimplexCore_iff (face_threshold_bound s hη hbound)).mpr
  refine ⟨((faceRegionProductHomeomorph s hη hbound).symm q).1.property, ⟨i, hi⟩, ?_⟩
  change η + (q.val i - η) / _ = η
  rw [he, sub_self, zero_div, add_zero]

theorem faceRegion_base_mem_intrinsicFrontier_of_overlap (s t : Finset ι)
    (hs : s.Nonempty) {η : ℝ} (hη : 0 ≤ η)
    (hbound : (Fintype.card ι : ℝ) * η < 1) (q : faceRegion s η)
    (ht : q.val ∈ faceRegion t η) (hne : s ≠ t) (hcard : t.card ≤ s.card) :
    (((faceRegionProductHomeomorph s hη hbound).symm q).1 : s → ℝ) ∈
      intrinsicFrontier ℝ (stdSimplexCore s η) := by
  obtain ⟨i, hi, _, he⟩ := exists_threshold_of_mem_faceRegions q.property ht hne hcard
  exact faceRegion_base_mem_intrinsicFrontier s hs hη hbound q hi he

end StdSimplexCore
