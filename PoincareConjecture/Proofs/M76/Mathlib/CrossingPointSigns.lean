import PoincareConjecture.Proofs.M76.Mathlib.RegularEdgeCrossing
import PoincareConjecture.Proofs.M76.Mathlib.BichromaticTriangle









set_option autoImplicit false

open Set

namespace AffineMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E]




theorem straddlesZero_neg_iff (A : E →ᵃ[ℝ] ℝ) (e : Finset E) :
    (-A).StraddlesZero e ↔ A.StraddlesZero e := by
  constructor
  · rintro ⟨u, v, hu, hv, he⟩
    refine ⟨v, u, ?_, ?_, he.trans (Set.pair_comm _ _)⟩
    · exact neg_pos.mp hv
    · exact neg_neg_iff_pos.mp hu
  · rintro ⟨u, v, hu, hv, he⟩
    exact ⟨v, u, neg_neg_of_pos hv, neg_pos.mpr hu, he.trans (Set.pair_comm _ _)⟩




theorem straddlingPoint_eq_zeroCrossing (A : E →ᵃ[ℝ] ℝ) {e : Finset E}
    (he : A.StraddlesZero e) {u v : E} (hu : A u < 0) (hv : 0 < A v)
    (heq : (e : Set E) = {u, v}) : A.straddlingPoint e he = A.zeroCrossing u v := by
  have hp := A.straddlingPoint_mem e he
  apply A.eq_zeroCrossing_of_mem_affineSpan (ne_of_lt (hu.trans hv))
  · apply convexHull_subset_affineSpan
    rw [← heq]
    exact hp.1
  · exact hp.2



theorem straddlingPoint_neg (A : E →ᵃ[ℝ] ℝ) {e : Finset E}
    (he : A.StraddlesZero e) (hne : (-A).StraddlesZero e) :
    (-A).straddlingPoint e hne = A.straddlingPoint e he := by
  apply (StraddlesZero.existsUnique A he).unique
  · have hp := (-A).straddlingPoint_mem e hne
    exact ⟨hp.1, neg_eq_zero.mp hp.2⟩
  · exact A.straddlingPoint_mem e he

variable [DecidableEq E]




theorem straddlesZero_iff_bichromatic (A : E →ᵃ[ℝ] ℝ) (e : Finset E)
    (hreg : ∀ u ∈ e, A u ≠ 0) :
    A.StraddlesZero e ↔ e.IsBichromaticPair (fun u => decide (0 < A u)) := by
  classical
  constructor
  · rintro ⟨u, v, hu, hv, he⟩
    refine ⟨u, v, by simp [not_lt.mpr hu.le, hv], ?_⟩
    exact Finset.coe_injective (by simpa only [Finset.coe_pair] using he)
  · rintro ⟨u, v, hcolor, rfl⟩
    have hu0 := hreg u (Finset.mem_insert_self _ _)
    have hv0 := hreg v (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    by_cases hu : 0 < A u <;> by_cases hv : 0 < A v
    · exact (hcolor (by simp [hu, hv])).elim
    · refine ⟨v, u, lt_of_le_of_ne (le_of_not_gt hv) hv0, hu, ?_⟩
      simpa only [Finset.coe_pair] using Set.pair_comm u v
    · exact ⟨u, v, lt_of_le_of_ne (le_of_not_gt hu) hu0, hv, Finset.coe_pair⟩
    · exact (hcolor (by simp [hu, hv])).elim

end AffineMap
