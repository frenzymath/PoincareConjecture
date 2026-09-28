import PoincareConjecture.Proofs.M76.Mathlib.FiniteGenericHeight
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialPolygon

set_option autoImplicit false

open Set

theorem affineIndependent_of_strict_height_peak {V E : Type*}
    [AddCommGroup V] [Module ℝ V] [AddTorsor V E]
    (L : E →ᵃ[ℝ] ℝ) {a b c : E} (hab : L a < L b) (hcb : L c < L b)
    (hinter : affineSegment ℝ a b ∩ affineSegment ℝ b c ⊆ {b}) :
    AffineIndependent ℝ ![a, b, c] := by
  rw [affineIndependent_iff_not_collinear_set]
  intro h
  rcases h.wbtw_or_wbtw_or_wbtw with h | h | h
  · have hb := h.map L
    rcases le_total (L a) (L c) with hac | hca
    · exact (not_le_of_gt hcb) ((wbtw_iff_of_le hac).mp hb).2
    · exact (not_le_of_gt hab) ((wbtw_iff_of_le hca).mp hb.symm).2
  · have hcb' : c = b := hinter ⟨h.symm, right_mem_affineSegment ℝ b c⟩
    exact (ne_of_lt hcb) (congrArg L hcb')
  · have hab' : a = b := hinter ⟨left_mem_affineSegment ℝ a b, h.symm⟩
    exact (ne_of_lt hab) (congrArg L hab')

namespace Polygon

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}

private theorem rotate_ne_self (i : Fin (n + 3)) : finRotate (n + 3) i ≠ i := by
  rw [finRotate_apply]
  intro h
  have h1 : (1 : Fin (n + 3)) = 0 := add_left_cancel
    (show i + 1 = i + 0 by simpa only [add_zero] using h)
  have hval := congrArg Fin.val h1
  change 1 % (n + 3) = 0 at hval
  rw [Nat.mod_eq_of_lt (by omega)] at hval
  exact Nat.one_ne_zero hval

private theorem rotate_twice_ne_self (i : Fin (n + 3)) :
    finRotate (n + 3) (finRotate (n + 3) i) ≠ i := by
  simp only [finRotate_apply, add_assoc]
  intro h
  have h2 : (1 : Fin (n + 3)) + 1 = 0 := add_left_cancel
    (show i + (1 + 1) = i + 0 by simpa only [add_zero] using h)
  have hval := congrArg Fin.val h2
  change (1 % (n + 3) + 1 % (n + 3)) % (n + 3) = 0 at hval
  rw [Nat.mod_eq_of_lt (by omega : 1 < n + 3)] at hval
  norm_num only [Nat.reduceAdd] at hval
  rw [Nat.mod_eq_of_lt (by omega)] at hval
  omega

theorem adjacent_edgeSet_inter (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P) (i : Fin (n + 3)) :
    P.edgeSet ℝ i ∩ P.edgeSet ℝ (finRotate (n + 3) i) = {P (finRotate (n + 3) i)} := by
  have h20 := hinj.ne (rotate_twice_ne_self i)
  have hvertices : (P.edgeVertices i : Set E) ∩
      P.edgeVertices (finRotate (n + 3) i) = {P (finRotate (n + 3) i)} := by
    ext x
    simp only [edgeVertices, Finset.coe_pair, mem_inter_iff, mem_insert_iff,
      mem_singleton_iff]
    constructor
    · rintro ⟨rfl | rfl, h | h⟩
      · exact h
      · exact (h20 h.symm).elim
      · rfl
      · rfl
    · rintro rfl
      exact ⟨Or.inr rfl, Or.inl rfl⟩
  apply Subset.antisymm
  · simpa only [hvertices, convexHull_singleton] using hP i (finRotate (n + 3) i)
  · rintro x rfl
    exact ⟨right_mem_affineSegment ℝ _ _, left_mem_affineSegment ℝ _ _⟩

theorem affineIndependent_at_strict_height_max (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    (L : E →ᵃ[ℝ] ℝ) (i : Fin (n + 3))
    (hmax : ∀ j, j ≠ i → L (P j) < L (P i)) :
    AffineIndependent ℝ
      ![P ((finRotate (n + 3)).symm i), P i, P (finRotate (n + 3) i)] := by
  have hprev : (finRotate (n + 3)).symm i ≠ i := by
    intro h
    exact rotate_ne_self i (by simpa only [Equiv.apply_symm_apply] using
      (congrArg (finRotate (n + 3)) h).symm)
  apply affineIndependent_of_strict_height_peak L (hmax _ hprev)
    (hmax _ (rotate_ne_self i))
  simpa only [edgeSet, Equiv.apply_symm_apply] using
    (P.adjacent_edgeSet_inter hP hinj ((finRotate (n + 3)).symm i)).subset

theorem exists_nondegenerate_strict_max (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P) :
    ∃ (L : E →ₗ[ℝ] ℝ) (i : Fin (n + 3)),
      Function.Injective (fun j => L (P j)) ∧
      (∀ j, j ≠ i → L (P j) < L (P i)) ∧
      AffineIndependent ℝ
        ![P ((finRotate (n + 3)).symm i), P i, P (finRotate (n + 3) i)] := by
  obtain ⟨L, i, hL, hi⟩ := P.exists_strict_max_height hinj
  exact ⟨L, i, hL, hi, P.affineIndependent_at_strict_height_max hP hinj L.toAffineMap i hi⟩

end Polygon
