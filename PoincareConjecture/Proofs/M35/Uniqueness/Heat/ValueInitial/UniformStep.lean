import PoincareConjecture.Proofs.M35.Uniqueness.Heat.PrincipalContinuousHeat

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set

namespace PoincareConjecture.M35.Uniqueness.Heat.ValueInitial

theorem exists_uniform_mixed_step {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {a b M : ℝ} (hM : 0 < M)
    (P : ℝ → E) (hPc : ContinuousOn P (Icc a b))
    (L : ℝ → F) (hLc : ContinuousOn L (Icc a b)) :
    ∃ q C τ : ℝ, 0 < q ∧ 0 < C ∧ 0 < τ ∧ τ ≤ 1 ∧
      (∀ s ∈ Icc a b, ∀ t ∈ Icc a b, |s - t| ≤ τ → ‖P s - P t‖ ≤ q) ∧
      (∀ t ∈ Icc a b, ‖L t‖ ≤ C) ∧
      (∀ T ∈ Icc 0 τ, (T + 1) * (M * (q * M)) +
        (Real.sqrt T * (Real.sqrt T + 1)) * (C * M) < 1) := by
  let q := 1 / (16 * M ^ 2)
  have hq : 0 < q := by dsimp only [q]; positivity
  have hqM : M * (q * M) = 1 / 16 := by
    dsimp only [q]
    field_simp
  obtain ⟨C, hC, hCb⟩ := (isCompact_Icc.image_of_continuousOn hLc).isBounded.exists_pos_norm_le
  have hPu := isCompact_Icc.uniformContinuousOn_of_continuous hPc
  obtain ⟨δ, hδ, hδb⟩ := Metric.uniformContinuousOn_iff.mp hPu q hq
  let f : ℝ → ℝ := fun t => Real.sqrt t * (C * M + 1)
  have hfc : ContinuousOn f (Icc 0 1) :=
    Real.continuous_sqrt.continuousOn.mul continuousOn_const
  obtain ⟨d, hd, hd1, _, hdb⟩ := exists_small_initial_interval f zero_lt_one
    (show (0 : ℝ) < 1 / 16 by norm_num) hfc
  let τ := min d (δ / 2)
  have hτ : 0 < τ := lt_min hd (half_pos hδ)
  have hτd : τ ≤ d := min_le_left _ _
  have hτδ : τ < δ := (min_le_right _ _).trans_lt (by linarith)
  refine ⟨q, C, τ, hq, hC, hτ, hτd.trans hd1, ?_, ?_, ?_⟩
  · intro s hs t ht hst
    have hdist : dist s t < δ := by
      simpa only [Real.dist_eq] using hst.trans_lt hτδ
    simpa only [dist_eq_norm] using (hδb s hs t ht hdist).le
  · intro t ht
    exact hCb _ ⟨t, ht, rfl⟩
  · intro T hT
    have hT1 : T ≤ 1 := hT.2.trans (hτd.trans hd1)
    have hroot : Real.sqrt T ≤ 1 := by
      nlinarith only [Real.sq_sqrt hT.1, Real.sqrt_nonneg T, hT1]
    have hg := hdb T ⟨hT.1, hT.2.trans hτd⟩
    have hf0 : f 0 = 0 := by simp only [f, Real.sqrt_zero, zero_mul]
    rw [hf0, sub_zero, Real.norm_eq_abs] at hg
    have hgain : Real.sqrt T * (C * M + 1) ≤ 1 / 16 :=
      (le_abs_self (f T)).trans hg
    have hmul := mul_le_mul_of_nonneg_right (show Real.sqrt T + 1 ≤ 2 by linarith)
      (mul_nonneg (Real.sqrt_nonneg T) (mul_nonneg hC.le hM.le))
    rw [hqM]
    nlinarith only [hgain, Real.sqrt_nonneg T, hT1, hmul]

end PoincareConjecture.M35.Uniqueness.Heat.ValueInitial
