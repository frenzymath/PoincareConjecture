import PoincareConjecture.Proofs.M76.Mathlib.ConvexRadialNormalization












set_option autoImplicit false

open Set NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]






theorem IsCompact.exists_frontier_and_interior_linear_sign
    {C : Set E} (hC : IsCompact C) (hcv : Convex ℝ C)
    (hzero : (0 : E) ∈ interior C) (A B : E →ₗ[ℝ] ℝ)
    {v : E} (hAv : A v = 0) (hBv : 0 < B v) :
    ∃ p q : E, p ∈ frontier C ∧ q ∈ interior C ∧
      A p = 0 ∧ 0 < B p ∧ A q = 0 ∧ 0 < B q := by
  have hv : v ≠ 0 := by
    intro hv
    rw [hv, map_zero] at hBv
    exact lt_irrefl 0 hBv
  obtain ⟨hr, hp⟩ := hC.gauge_inv_smul_mem_frontier hcv hzero hv
  let p : E := (gauge C v)⁻¹ • v
  have hAp : A p = 0 := by
    dsimp [p]
    rw [map_smul, hAv, smul_zero]
  have hBp : 0 < B p := by
    dsimp [p]
    rw [map_smul, smul_eq_mul]
    exact mul_pos hr hBv
  have hq : midpoint ℝ (0 : E) p ∈ interior C :=
    hcv.openSegment_interior_self_subset_interior hzero
      (hC.isClosed.frontier_subset hp) (midpoint_mem_openSegment 0 p)
  have hmid (L : E →ₗ[ℝ] ℝ) : L (midpoint ℝ (0 : E) p) = L p / 2 := by
    rw [midpoint_eq_smul_add]
    simp only [map_smul, map_add, map_zero, zero_add, invOf_eq_inv, smul_eq_mul]
    ring
  refine ⟨p, midpoint ℝ (0 : E) p, hp, hq, hAp, hBp, ?_, ?_⟩
  · rw [hmid, hAp, zero_div]
  · rw [hmid]
    exact half_pos hBp





theorem Convex.frontier_inter_coordinate_planes_eq_poles
    {C : Set ((ℝ × ℝ) × ℝ)} (hcv : Convex ℝ C)
    (hzero : (0 : (ℝ × ℝ) × ℝ) ∈ interior C)
    {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    (haC : ((0, a), 0) ∈ frontier C) (hbC : ((0, b), 0) ∈ frontier C) :
    frontier C ∩ {x | x.1.1 = 0 ∧ x.2 = 0} =
      {((0, a), 0), ((0, b), 0)} := by
  apply Subset.antisymm
  · intro x hx
    have hx0 : x ≠ 0 := fun heq => hx.1.2 (heq ▸ hzero)
    have hy0 : x.1.2 ≠ 0 := by
      intro hy
      exact hx0 (Prod.ext (Prod.ext hx.2.1 hy) hx.2.2)
    have hdecomp (r : ℝ) (hr : r ≠ 0) :
        x = (x.1.2 / r) • (((0, r), 0) : (ℝ × ℝ) × ℝ) := by
      apply Prod.ext
      · apply Prod.ext
        · simpa only [Prod.smul_fst, smul_eq_mul, mul_zero] using hx.2.1
        · simpa only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] using
            (div_mul_cancel₀ x.1.2 hr).symm
      · simpa only [Prod.smul_snd, smul_eq_mul, mul_zero] using hx.2.2
    rcases lt_or_gt_of_ne hy0 with hyneg | hypos
    · have heq : x = ((0, a), 0) := by
        apply hcv.injOn_normalize_frontier hzero hx.1 haC
        rw [hdecomp a ha.ne, normalize_smul_of_pos (div_pos_of_neg_of_neg hyneg ha)]
      exact Or.inl heq
    · have heq : x = ((0, b), 0) := by
        apply hcv.injOn_normalize_frontier hzero hx.1 hbC
        rw [hdecomp b hb.ne', normalize_smul_of_pos (div_pos hypos hb)]
      exact Or.inr heq
  · rintro x (rfl | rfl)
    · exact ⟨haC, rfl, rfl⟩
    · exact ⟨hbC, rfl, rfl⟩
