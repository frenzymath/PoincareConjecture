import PoincareConjecture.Proofs.M25.Topology3D.Polygon.CyclicArc











set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

variable {n : ℕ}


def cyclicDistance (a b : Fin n) : ℕ := (b - a).val


theorem cyclicDistance_lt (a b : Fin n) : cyclicDistance a b < n := (b - a).isLt


theorem iterate_cyclicDistance (a b : Fin n) :
    (finRotate n)^[cyclicDistance a b] a = b := by
  let : NeZero n := a.neZero
  calc
    _ = a + (b - a) := by
      simpa only [cyclicDistance, finCycle_apply] using
        (congrFun (finCycle_eq_finRotate_iterate (k := b - a)) a).symm
    _ = b := by abel


theorem cyclicDistance_iterate (a : Fin n) (t : ℕ) (ht : t < n) :
    cyclicDistance a ((finRotate n)^[t] a) = t := by
  let : NeZero n := a.neZero
  have hrot : (finRotate n)^[t] a = a + (⟨t, ht⟩ : Fin n) := by
    simpa only [finCycle_apply] using
      (congrFun (finCycle_eq_finRotate_iterate (k := (⟨t, ht⟩ : Fin n))) a).symm
  simp only [cyclicDistance, hrot, add_sub_cancel_left]


theorem cyclicDistance_self (a : Fin n) : cyclicDistance a a = 0 := by
  let : NeZero n := a.neZero
  simp [cyclicDistance]


theorem cyclicDistance_add_reverse (a b : Fin n) (hab : b ≠ a) :
    cyclicDistance a b + cyclicDistance b a = n := by
  let : NeZero n := a.neZero
  have hne : b - a ≠ 0 := sub_ne_zero.mpr hab
  have hneg : a - b = -(b - a) := by abel
  change (b - a).val + (a - b).val = n
  rw [hneg, Fin.val_neg, if_neg hne]
  have := (b - a).isLt
  omega


theorem cyclicDistance_change_start (a b i : Fin n) :
    cyclicDistance b i = if cyclicDistance a i < cyclicDistance a b then
      n + cyclicDistance a i - cyclicDistance a b else
      cyclicDistance a i - cyclicDistance a b := by
  let : NeZero n := a.neZero
  have hsub : i - b = (i - a) - (b - a) := by abel
  unfold cyclicDistance
  rw [hsub]
  split_ifs with h
  · exact Fin.coe_sub_iff_lt.mpr h
  · exact Fin.sub_val_of_le (not_lt.mp h)


theorem cyclicDistance_nonadjacent_bounds (a b : Fin n) (hab : b ≠ a)
    (hs : b ≠ finRotate n a) (hp : b ≠ (finRotate n).symm a) :
    2 ≤ cyclicDistance a b ∧ cyclicDistance a b + 1 < n := by
  have htwo (c d : Fin n) (hne : d ≠ c) (hnext : d ≠ finRotate n c) :
      2 ≤ cyclicDistance c d := by
    by_contra h
    have hsmall : cyclicDistance c d = 0 ∨ cyclicDistance c d = 1 := by omega
    have hreach := iterate_cyclicDistance c d
    rcases hsmall with hsmall | hsmall
    · rw [hsmall] at hreach
      exact hne hreach.symm
    · rw [hsmall] at hreach
      exact hnext hreach.symm
  have hforward := htwo a b hab hs
  have hreverse := htwo b a hab.symm (by
    intro h
    apply hp
    simpa only [Equiv.symm_apply_apply] using (congrArg (finRotate n).symm h).symm)
  have hsum := cyclicDistance_add_reverse a b hab
  exact ⟨hforward, by omega⟩


theorem mem_range_cyclicArcIndex_iff (a : Fin n) (m : ℕ) (hm : m < n) (i : Fin n) :
    i ∈ range (cyclicArcIndex a m) ↔ cyclicDistance a i ≤ m := by
  constructor
  · rintro ⟨j, rfl⟩
    change cyclicDistance a ((finRotate n)^[j.val] a) ≤ m
    rw [cyclicDistance_iterate a j.val (by omega)]
    omega
  · intro hi
    exact ⟨⟨cyclicDistance a i, by omega⟩, iterate_cyclicDistance a i⟩


theorem mem_range_cyclicArcEdgeIndex_iff (a : Fin n) (m : ℕ) (hm : m < n) (i : Fin n) :
    i ∈ range (fun j : Fin m => cyclicArcIndex a m j.castSucc) ↔ cyclicDistance a i < m := by
  constructor
  · rintro ⟨j, rfl⟩
    change cyclicDistance a ((finRotate n)^[j.val] a) < m
    rw [cyclicDistance_iterate a j.val (j.isLt.trans hm)]
    exact j.isLt
  · intro hi
    exact ⟨⟨cyclicDistance a i, hi⟩, iterate_cyclicDistance a i⟩


theorem cyclicArc_edgeIndex_partition (a b : Fin n) (hab : b ≠ a) :
    Disjoint
      (range (fun i : Fin (cyclicDistance a b) =>
        cyclicArcIndex a (cyclicDistance a b) i.castSucc))
      (range (fun i : Fin (cyclicDistance b a) =>
        cyclicArcIndex b (cyclicDistance b a) i.castSucc)) ∧
    range (fun i : Fin (cyclicDistance a b) =>
      cyclicArcIndex a (cyclicDistance a b) i.castSucc) ∪
    range (fun i : Fin (cyclicDistance b a) =>
      cyclicArcIndex b (cyclicDistance b a) i.castSucc) = univ := by
  have hsum := cyclicDistance_add_reverse a b hab
  have hfirst := mem_range_cyclicArcEdgeIndex_iff a _ (cyclicDistance_lt a b)
  have hsecond := mem_range_cyclicArcEdgeIndex_iff b _ (cyclicDistance_lt b a)
  refine ⟨Set.disjoint_left.mpr ?_, subset_antisymm (subset_univ _) ?_⟩
  · intro i hi hj
    have hti := (hfirst i).mp hi
    have hui := (hsecond i).mp hj
    have hchange := cyclicDistance_change_start a b i
    rw [if_pos hti] at hchange
    omega
  · intro i _
    by_cases hi : cyclicDistance a i < cyclicDistance a b
    · exact Or.inl ((hfirst i).mpr hi)
    · apply Or.inr
      apply (hsecond i).mpr
      have hchange := cyclicDistance_change_start a b i
      rw [if_neg hi] at hchange
      have := cyclicDistance_lt a i
      omega


theorem cyclicArc_vertexIndex_inter (a b : Fin n) (hab : b ≠ a) :
    range (cyclicArcIndex a (cyclicDistance a b)) ∩
      range (cyclicArcIndex b (cyclicDistance b a)) = {a, b} := by
  have hsum := cyclicDistance_add_reverse a b hab
  have hfirst := mem_range_cyclicArcIndex_iff a _ (cyclicDistance_lt a b)
  have hsecond := mem_range_cyclicArcIndex_iff b _ (cyclicDistance_lt b a)
  apply subset_antisymm
  · intro i hi
    have ht := (hfirst i).mp hi.1
    have hu := (hsecond i).mp hi.2
    have hchange := cyclicDistance_change_start a b i
    have hreach := iterate_cyclicDistance a i
    by_cases hlt : cyclicDistance a i < cyclicDistance a b
    · rw [if_pos hlt] at hchange
      have hzero : cyclicDistance a i = 0 := by omega
      rw [hzero] at hreach
      exact Or.inl hreach.symm
    · have heq : cyclicDistance a i = cyclicDistance a b := by omega
      rw [heq] at hreach
      exact Or.inr (hreach.symm.trans (iterate_cyclicDistance a b))
  · intro i hi
    rcases hi with hi | hi
    · change i = a at hi
      subst i
      exact ⟨(hfirst a).mpr (by rw [cyclicDistance_self]; omega),
        (hsecond a).mpr le_rfl⟩
    · change i = b at hi
      subst i
      exact ⟨(hfirst b).mpr le_rfl,
        (hsecond b).mpr (by rw [cyclicDistance_self]; omega)⟩

end PoincareConjecture.M25.Topology3D
