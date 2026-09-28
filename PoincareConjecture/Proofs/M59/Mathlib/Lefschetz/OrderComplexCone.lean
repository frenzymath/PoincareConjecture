import PoincareConjecture.Proofs.M59.Mathlib.Lefschetz.OrderComplexNeighborhoods

set_option autoImplicit false

noncomputable section

open scoped BigOperators unitInterval

universe u

namespace PoincareConjecture.Proofs.M59

open M02.Topology

variable {J : Type u} [PartialOrder J] [Fintype J]

open scoped Classical in

def orderComplexVertex (v : J) : (finiteOrderComplex J).space := by
  refine ⟨fun i => if i = v then 1 else 0, ?_⟩
  have h := (orderComplexStar_barycenter_mem ({v} : Finset J)
    (Finset.singleton_nonempty v) (by simp)).1
  simpa only [Finset.card_singleton, Nat.cast_one, inv_one, Finset.mem_singleton] using h

def orderComplexConePoint (s : Finset J) (v : J) (hv : v ∈ s) :
    orderComplexNeighborhood s := by
  classical
  refine ⟨orderComplexVertex v, ?_⟩
  apply (mem_orderComplexNeighborhood_iff s _).mpr
  exact ⟨v, hv, by simp [orderComplexVertex]⟩

variable (s : Finset J) (v : J) (hv : v ∈ s) (hmin : ∀ j ∈ s, v ≤ j)

include hv hmin

open scoped Classical in

theorem orderComplexConeSegment_mem (z : orderComplexNeighborhood s) (t : I) :
    let w := fun i => (1 - (t : ℝ)) * orderComplexRestrictionCoord s z.val.val i +
      (t : ℝ) * (orderComplexVertex v).val i
    w ∈ (finiteOrderComplex J).space ∧ orderComplexRestrictionWeight s w = 1 := by
  classical
  let r := orderComplexRestrictionCoord s z.val.val
  let w := fun i => (1 - (t : ℝ)) * r i + (t : ℝ) * (orderComplexVertex v).val i
  have hr := (finiteOrderComplex_space J r).mp (orderComplexRestrictionCoord_mem s z)
  have hvertex := (finiteOrderComplex_space J _).mp (orderComplexVertex v).property
  have hsupp (i : J) (hi : i ∉ s) : w i = 0 := by
    have hiv : i ≠ v := fun h => hi (h ▸ hv)
    simp only [w, r, orderComplexRestrictionCoord, if_neg hi, orderComplexVertex,
      if_neg hiv, mul_zero, add_zero]
  have hri (i : J) (hi : w i ≠ 0) (hiv : i ≠ v) : r i ≠ 0 := by
    intro h
    simp only [w, h, orderComplexVertex, if_neg hiv, mul_zero, add_zero] at hi
    exact hi rfl
  have hmem : w ∈ (finiteOrderComplex J).space := by
    apply (finiteOrderComplex_space J _).mpr
    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) (hr.1 i))
        (mul_nonneg t.property.1 (hvertex.1 i))
    · change (∑ i : J, ((1 - (t : ℝ)) * r i + (t : ℝ) * (orderComplexVertex v).val i)) = 1
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        hr.2.1, hvertex.2.1]
      ring
    · intro i j hi hj
      by_cases hiv : i = v
      · subst i
        exact Or.inl (hmin j (by by_contra h; exact hj (hsupp j h)))
      by_cases hjv : j = v
      · subst j
        exact Or.inr (hmin i (by by_contra h; exact hi (hsupp i h)))
      · exact hr.2.2 i j (hri i hi hiv) (hri j hj hjv)
  exact ⟨hmem, orderComplexRestrictionWeight_eq_one s ⟨w, hmem⟩ hsupp⟩

def orderComplexConeSecondHomotopy : (orderComplexRestriction s).Homotopy
    (ContinuousMap.const _ (orderComplexConePoint s v hv)) := by
  classical
  refine {
    toFun := fun q => ⟨⟨fun i => (1 - (q.1 : ℝ)) *
      orderComplexRestrictionCoord s q.2.val.val i + (q.1 : ℝ) * (orderComplexVertex v).val i,
      (orderComplexConeSegment_mem s v hv hmin q.2 q.1).1⟩, ?_⟩
    continuous_toFun := ?_
    map_zero_left := ?_
    map_one_left := ?_ }
  · change 0 < orderComplexRestrictionWeight s _
    rw [(orderComplexConeSegment_mem s v hv hmin q.2 q.1).2]
    exact zero_lt_one
  · apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      ((continuous_apply i).comp
        ((continuous_orderComplexRestrictionCoord s).comp continuous_snd))).add
      ((continuous_subtype_val.comp continuous_fst).mul continuous_const)
  · intro z
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change (1 - (0 : ℝ)) * orderComplexRestrictionCoord s z.val.val i +
      0 * (orderComplexVertex v).val i = orderComplexRestrictionCoord s z.val.val i
    ring
  · intro z
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change (1 - (1 : ℝ)) * orderComplexRestrictionCoord s z.val.val i +
      1 * (orderComplexVertex v).val i = (orderComplexVertex v).val i
    ring

def orderComplexConeHomotopy :
    (ContinuousMap.id (orderComplexNeighborhood s)).Homotopy
      (ContinuousMap.const _ (orderComplexConePoint s v hv)) :=
  (orderComplexRestrictionHomotopy s).trans (orderComplexConeSecondHomotopy s v hv hmin)

theorem orderComplexConeHomotopy_fixed (t : I) :
    orderComplexConeHomotopy s v hv hmin (t, orderComplexConePoint s v hv) =
      orderComplexConePoint s v hv := by
  classical
  have hsupp : ∀ i ∉ s, (orderComplexConePoint s v hv).val.val i = 0 := by
    intro i hi
    change (if i = v then (1 : ℝ) else 0) = 0
    exact if_neg (fun h : i = v => hi (h.symm ▸ hv))
  change ((orderComplexRestrictionHomotopy s).trans
    (orderComplexConeSecondHomotopy s v hv hmin)) (t, _) = _
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact orderComplexRestrictionHomotopy_fixed s _ hsupp _
  · apply Subtype.ext
    apply Subtype.ext
    change (fun i => (1 - _) * orderComplexRestrictionCoord s
      (orderComplexConePoint s v hv).val.val i + _ * (orderComplexVertex v).val i) = _
    rw [orderComplexRestrictionCoord_eq_self s _ hsupp]
    funext i
    change (1 - _) * (orderComplexVertex v).val i + _ * (orderComplexVertex v).val i =
      (orderComplexVertex v).val i
    ring

end PoincareConjecture.Proofs.M59
