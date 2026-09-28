import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionFrontier










set_option autoImplicit false
open Set Metric

namespace PoincareConjecture.M76.Dehn

theorem affine_lt_on_closure_of_lt_frontier
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    {U : Set E} (hU : IsOpen U) (hbounded : Bornology.IsBounded U)
    (A : E →ᵃ[ℝ] ℝ) (v : E) (hv : 0 < A.linear v) {a : ℝ}
    (hfront : ∀ x ∈ frontier U, A x < a) : ∀ x ∈ closure U, A x < a := by
  intro x hx
  have hne : U.Nonempty := closure_nonempty_iff.mp ⟨x, hx⟩
  have hproper : U ≠ univ := by
    intro h
    exact NormedSpace.unbounded_univ ℝ E (h ▸ hbounded)
  have hfrontne : (frontier U).Nonempty := nonempty_frontier_iff.mpr ⟨hne, hproper⟩
  have hcompact : IsCompact (frontier U) :=
    hbounded.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨y, hy, hmax⟩ := hcompact.exists_isMaxOn hfrontne
    A.continuous_of_finiteDimensional.continuousOn
  exact (hU.affine_le_on_closure_of_le_frontier hbounded A v hv hmax x hx).trans_lt
    (hfront y hy)


theorem closure_subset_product_cube_of_frontier_subset
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {U : Set ((ι → ℝ) × (κ → ℝ))} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hU : IsOpen U) (hbounded : Bornology.IsBounded U)
    (hfront : frontier U ⊆ closedBall (0 : ι → ℝ) a ×ˢ closedBall (0 : κ → ℝ) b) :
    closure U ⊆ closedBall (0 : ι → ℝ) a ×ˢ closedBall (0 : κ → ℝ) b := by
  classical
  intro x hx
  constructor
  · rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg ha]
    intro i
    let A : ((ι → ℝ) × (κ → ℝ)) →ᵃ[ℝ] ℝ :=
      ((ContinuousLinearMap.proj i).comp
        (ContinuousLinearMap.fst ℝ (ι → ℝ) (κ → ℝ))).toLinearMap.toAffineMap
    let v : (ι → ℝ) × (κ → ℝ) := (Pi.single i 1, 0)
    have hv : A.linear v = 1 := by simp [A, v]
    have hpos := hU.affine_le_on_closure_of_le_frontier hbounded A v (by rw [hv]; norm_num)
      (fun y hy ↦ (abs_le.mp ((pi_norm_le_iff_of_nonneg ha).mp
        (mem_closedBall_zero_iff.mp (hfront hy).1) i)).2) x hx
    have hneg := hU.affine_le_on_closure_of_le_frontier hbounded (-A) (-v)
      (by simpa using (show 0 < A.linear v by rw [hv]; norm_num))
      (a := a) (fun y hy ↦ by
        have h := (abs_le.mp ((pi_norm_le_iff_of_nonneg ha).mp
          (mem_closedBall_zero_iff.mp (hfront hy).1) i)).1
        change -(y.1 i) ≤ a
        linarith) x hx
    exact abs_le.mpr ⟨by change -(x.1 i) ≤ a at hneg; linarith, hpos⟩
  · rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hb]
    intro i
    let A : ((ι → ℝ) × (κ → ℝ)) →ᵃ[ℝ] ℝ :=
      ((ContinuousLinearMap.proj i).comp
        (ContinuousLinearMap.snd ℝ (ι → ℝ) (κ → ℝ))).toLinearMap.toAffineMap
    let v : (ι → ℝ) × (κ → ℝ) := (0, Pi.single i 1)
    have hv : A.linear v = 1 := by simp [A, v]
    have hpos := hU.affine_le_on_closure_of_le_frontier hbounded A v (by rw [hv]; norm_num)
      (fun y hy ↦ (abs_le.mp ((pi_norm_le_iff_of_nonneg hb).mp
        (mem_closedBall_zero_iff.mp (hfront hy).2) i)).2) x hx
    have hneg := hU.affine_le_on_closure_of_le_frontier hbounded (-A) (-v)
      (by simpa using (show 0 < A.linear v by rw [hv]; norm_num))
      (a := b) (fun y hy ↦ by
        have h := (abs_le.mp ((pi_norm_le_iff_of_nonneg hb).mp
          (mem_closedBall_zero_iff.mp (hfront hy).2) i)).1
        change -(y.2 i) ≤ b
        linarith) x hx
    exact abs_le.mpr ⟨by change -(x.2 i) ≤ b at hneg; linarith, hpos⟩



theorem closure_subset_transverse_ball_of_frontier_subset
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {U : Set ((ι → ℝ) × (κ → ℝ))} {b : ℝ}
    (hb : 0 < b) (hU : IsOpen U) (hbounded : Bornology.IsBounded U)
    (hfront : frontier U ⊆ (univ : Set (ι → ℝ)) ×ˢ ball (0 : κ → ℝ) b) :
    closure U ⊆ (univ : Set (ι → ℝ)) ×ˢ ball (0 : κ → ℝ) b := by
  classical
  intro x hx
  refine ⟨mem_univ _, ?_⟩
  rw [mem_ball_zero_iff, pi_norm_lt_iff hb]
  intro i
  let : Nonempty κ := ⟨i⟩
  let A : ((ι → ℝ) × (κ → ℝ)) →ᵃ[ℝ] ℝ :=
    ((ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.snd ℝ (ι → ℝ) (κ → ℝ))).toLinearMap.toAffineMap
  let v : (ι → ℝ) × (κ → ℝ) := (0, Pi.single i 1)
  have hv : A.linear v = 1 := by simp [A, v]
  have hpos := affine_lt_on_closure_of_lt_frontier hU hbounded A v (by rw [hv]; norm_num)
    (fun y hy ↦ (abs_lt.mp ((pi_norm_lt_iff hb).mp
      (mem_ball_zero_iff.mp (hfront hy).2) i)).2) x hx
  have hneg := affine_lt_on_closure_of_lt_frontier hU hbounded (-A) (-v)
    (by simpa using (show 0 < A.linear v by rw [hv]; norm_num))
    (a := b) (fun y hy ↦ by
      have h := (abs_lt.mp ((pi_norm_lt_iff hb).mp
        (mem_ball_zero_iff.mp (hfront hy).2) i)).1
      change -(y.2 i) < b
      linarith) x hx
  exact abs_lt.mpr ⟨by change -(x.2 i) < b at hneg; linarith, hpos⟩

end PoincareConjecture.M76.Dehn
