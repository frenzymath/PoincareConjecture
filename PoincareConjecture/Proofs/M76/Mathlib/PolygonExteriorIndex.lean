import PoincareConjecture.Proofs.M76.Mathlib.PolygonBoundedRegions









set_option autoImplicit false

open Set Metric PlanarSegment
open scoped BigOperators

namespace Polygon

variable {n : ℕ} (P : Polygon (ℝ × ℝ) n)



theorem crossingIndex_eq_on_preconnected (hnv : P.HasNonverticalEdges)
    {S : Set (ℝ × ℝ)} (hS : IsPreconnected S) (hsub : S ⊆ (P.boundary ℝ)ᶜ)
    {x y : ℝ × ℝ} (hx : x ∈ S) (hy : y ∈ S) :
    P.crossingIndex x = P.crossingIndex y := by
  let : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hS
  let f : S → ↥((P.boundary ℝ)ᶜ) := fun q => ⟨q.val, hsub q.property⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  exact ((P.isLocallyConstant_crossingIndex hnv).comp_continuous hf).apply_eq_of_preconnectedSpace
    ⟨x, hx⟩ ⟨y, hy⟩



theorem crossingIndex_eq_zero_of_left {q : ℝ × ℝ}
    (hq : ∀ i, q.1 < (P i).1) : P.crossingIndex q = 0 := by
  unfold crossingIndex
  apply Finset.sum_eq_zero
  intro i _
  simp only [crossingContribution, horizontalStep, if_neg (not_le_of_gt (hq i)),
    if_neg (not_le_of_gt (hq (finRotate n i))), sub_self, zero_mul]




theorem crossingIndex_eq_zero_of_unbounded_component (hnv : P.HasNonverticalEdges)
    {x : ℝ × ℝ} (hx : x ∈ (P.boundary ℝ)ᶜ)
    (hunbounded : ¬ Bornology.IsBounded (connectedComponentIn (P.boundary ℝ)ᶜ x)) :
    P.crossingIndex x = 0 := by
  obtain ⟨r, hr, hbound⟩ := P.isCompact_boundary.isBounded.subset_closedBall_lt 0 (0 : ℝ × ℝ)
  have hdim : 1 < Module.rank ℝ (ℝ × ℝ) := by
    rw [← Module.finrank_eq_rank]
    norm_num [Module.finrank_prod]
  have hinter : ((closedBall (0 : ℝ × ℝ) r)ᶜ ∩
      connectedComponentIn (P.boundary ℝ)ᶜ x).Nonempty := by
    by_contra h
    apply hunbounded
    apply (isBounded_closedBall (x := (0 : ℝ × ℝ)) (r := r)).subset
    intro y hy
    by_contra hyr
    exact h ⟨y, hyr, hy⟩
  have hc := (isConnected_compl_closedBall_zero hdim r).isPreconnected
  have hext : (closedBall (0 : ℝ × ℝ) r)ᶜ ⊆
      connectedComponentIn (P.boundary ℝ)ᶜ x :=
    hc.subset_connectedComponentIn_of_inter_nonempty
      (compl_subset_compl.mpr hbound) hinter
  let q : ℝ × ℝ := (-r - 1, 0)
  have hqnorm : r < ‖q‖ := by
    have hfst := norm_fst_le q
    have hneg : -r - 1 < 0 := by linarith
    simp only [q, Real.norm_eq_abs, abs_of_neg hneg] at hfst
    linarith
  have hqC : q ∈ connectedComponentIn (P.boundary ℝ)ᶜ x :=
    hext (by simpa only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] using hqnorm)
  have hleft (i : Fin n) : q.1 < (P i).1 := by
    have hi : P i ∈ P.boundary ℝ := mem_iUnion.mpr ⟨i, left_mem_affineSegment ℝ _ _⟩
    have hnorm : ‖P i‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hbound hi
    have hfst : |(P i).1| ≤ r := (norm_fst_le (P i)).trans hnorm
    have hlow := (abs_le.mp hfst).1
    change -r - 1 < (P i).1
    linarith
  calc
    P.crossingIndex x = P.crossingIndex q :=
      P.crossingIndex_eq_on_preconnected hnv isPreconnected_connectedComponentIn
        (connectedComponentIn_subset _ _) (mem_connectedComponentIn hx) hqC
    _ = 0 := P.crossingIndex_eq_zero_of_left hleft

end Polygon
