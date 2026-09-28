import PoincareConjecture.Proofs.M76.Mathlib.ZeroApexSlice
import PoincareConjecture.Proofs.M76.Mathlib.CrossingPointSigns










set_option autoImplicit false

open Set

namespace AffineMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E]





theorem convexHull_zero_apex_pair_inter_zero (A : E →ᵃ[ℝ] ℝ) {q u v : E}
    (hq : A q = 0) (hu : A u < 0) (hv : 0 < A v) :
    convexHull ℝ (insert q ({u, v} : Set E)) ∩ {x | A x = 0} =
      segment ℝ q (A.zeroCrossing u v) := by
  rw [A.convexHull_insert_inter_zero_of_zero hq,
    A.convexHull_pair_inter_zero hu hv, convexHull_pair]




theorem convexHull_zero_apex_pair_inter_zero_of_pos (A : E →ᵃ[ℝ] ℝ) {q u v : E}
    (hq : A q = 0) (hu : 0 < A u) (hv : 0 < A v) :
    convexHull ℝ (insert q ({u, v} : Set E)) ∩ {x | A x = 0} = {q} := by
  have hbase : convexHull ℝ ({u, v} : Set E) ∩ {x | A x = 0} = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hpos : 0 < A x := convexHull_min
      (by intro y hy; rcases hy with rfl | rfl <;> assumption)
      ((convex_Ioi (0 : ℝ)).affine_preimage A) hx.1
    exact (hx.2 ▸ hpos).false
  rw [A.convexHull_insert_inter_zero_of_zero hq, hbase, insert_empty_eq, convexHull_singleton]




theorem convexHull_zero_apex_pair_inter_zero_of_neg (A : E →ᵃ[ℝ] ℝ) {q u v : E}
    (hq : A q = 0) (hu : A u < 0) (hv : A v < 0) :
    convexHull ℝ (insert q ({u, v} : Set E)) ∩ {x | A x = 0} = {q} := by
  simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero] using
    (-A).convexHull_zero_apex_pair_inter_zero_of_pos
      (by simpa using hq) (neg_pos.mpr hu) (neg_pos.mpr hv)





theorem exceptional_triangle_slice_eq_singleton_or_segment
    [DecidableEq E] (A : E →ᵃ[ℝ] ℝ) {t : Finset E} (ht : t.card = 3) {q : E}
    (hqt : q ∈ t) (hq : A q = 0) (hreg : ∀ v ∈ t, v ≠ q → A v ≠ 0) :
    convexHull ℝ (t : Set E) ∩ {x | A x = 0} = {q} ∨
      ∃ he : A.StraddlesZero (t.erase q),
        convexHull ℝ (t : Set E) ∩ {x | A x = 0} =
          segment ℝ q (A.straddlingPoint (t.erase q) he) := by
  classical
  have hc : (t.erase q).card = 2 := by rw [Finset.card_erase_of_mem hqt, ht]
  obtain ⟨u, v, _, huv⟩ := Finset.card_eq_two.mp hc
  have hut : u ∈ t.erase q := by rw [huv]; simp
  have hvt : v ∈ t.erase q := by rw [huv]; simp
  have hu := hreg u (Finset.mem_erase.mp hut).2 (Finset.mem_erase.mp hut).1
  have hv := hreg v (Finset.mem_erase.mp hvt).2 (Finset.mem_erase.mp hvt).1
  have htrep : (t : Set E) = insert q {u, v} := by
    have he : t = insert q {u, v} := by rw [← huv, Finset.insert_erase hqt]
    rw [he, Finset.coe_insert, Finset.coe_pair]
  rcases lt_or_gt_of_ne hu with hu | hu <;> rcases lt_or_gt_of_ne hv with hv | hv
  · exact Or.inl (by rw [htrep]; exact A.convexHull_zero_apex_pair_inter_zero_of_neg hq hu hv)
  · have he : A.StraddlesZero (t.erase q) :=
      ⟨u, v, hu, hv, by rw [huv, Finset.coe_pair]⟩
    refine Or.inr ⟨he, ?_⟩
    rw [A.straddlingPoint_eq_zeroCrossing he hu hv (by rw [huv, Finset.coe_pair]), htrep]
    exact A.convexHull_zero_apex_pair_inter_zero hq hu hv
  · have heq : (↑(t.erase q) : Set E) = {v, u} := by
      rw [huv, Finset.coe_pair, Set.pair_comm]
    have he : A.StraddlesZero (t.erase q) := ⟨v, u, hv, hu, heq⟩
    refine Or.inr ⟨he, ?_⟩
    rw [A.straddlingPoint_eq_zeroCrossing he hv hu heq, htrep, Set.pair_comm u v]
    exact A.convexHull_zero_apex_pair_inter_zero hq hv hu
  · exact Or.inl (by rw [htrep]; exact A.convexHull_zero_apex_pair_inter_zero_of_pos hq hu hv)

end AffineMap
