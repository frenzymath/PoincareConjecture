import PoincareConjecture.Proofs.M35.Mathlib.HighCurvatureInterval

set_option autoImplicit false

open Filter Set
open scoped Topology

theorem exists_uniform_final_reciprocal_bound
    {X : Type*} {f f' : X → ℝ → ℝ} {A H : ℝ} (hA : 0 < A) (hH : 0 < H)
    (hpos : ∀ x t, t ∈ Ico 0 1 → 0 < f x t)
    (hderiv : ∀ x t, t ∈ Ico 0 1 → HasDerivWithinAt (f x) (f' x t) (Ico 0 1) t)
    (hbound : ∀ x t, t ∈ Ico 0 1 → H ≤ f x t → f' x t ≤ A * (f x t) ^ 2)
    (hblow : ∀ x, Tendsto (f x) (𝓝[<] 1) atTop) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 / 2 ∧
      ∀ x t, t ∈ Ico (1 - τ) 1 → (A * (1 - t))⁻¹ ≤ f x t := by
  let τ : ℝ := min (1 / 2) ((A * H)⁻¹ / 2)
  have hτ : 0 < τ := lt_min (by norm_num) (half_pos (inv_pos.mpr (mul_pos hA hH)))
  have hτhalf : τ ≤ 1 / 2 := min_le_left _ _
  have hτbound : A * H * τ ≤ 1 / 2 := by
    calc
      A * H * τ ≤ A * H * ((A * H)⁻¹ / 2) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (mul_pos hA hH).le
      _ = 1 / 2 := by rw [← mul_div_assoc, mul_inv_cancel₀ (mul_pos hA hH).ne']
  refine ⟨τ, hτ, hτhalf, ?_⟩
  intro x t ht
  have ht₀ : t ∈ Ico 0 1 := ⟨by linarith [ht.1], ht.2⟩
  apply inv_mul_time_sub_le_of_eventual_quadratic_bound hA hH
    (hpos x) (hderiv x) (hbound x) (hblow x) ht₀
  have htime : A * H * (1 - t) ≤ A * H * τ :=
    mul_le_mul_of_nonneg_left (by linarith [ht.1]) (mul_pos hA hH).le
  linarith

theorem exists_uniform_reciprocal_bound_of_early_floor
    {X : Type*} {f : X → ℝ → ℝ} {A B τ : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hτ : 0 < τ)
    (hearly : ∀ x t, t ∈ Icc 0 (1 - τ) → B ≤ f x t)
    (hfinal : ∀ x t, t ∈ Ico (1 - τ) 1 → (A * (1 - t))⁻¹ ≤ f x t) :
    ∃ c : ℝ, 0 < c ∧ ∀ x t, t ∈ Ico 0 1 → c / (1 - t) ≤ f x t := by
  refine ⟨min A⁻¹ (B * τ), lt_min (inv_pos.mpr hA) (mul_pos hB hτ), ?_⟩
  intro x t ht
  have hden : 0 < 1 - t := sub_pos.mpr ht.2
  by_cases hlate : 1 - τ ≤ t
  · calc
      min A⁻¹ (B * τ) / (1 - t) ≤ A⁻¹ / (1 - t) :=
        div_le_div_of_nonneg_right (min_le_left _ _) hden.le
      _ = (A * (1 - t))⁻¹ := by rw [div_eq_mul_inv, mul_inv]
      _ ≤ f x t := hfinal x t ⟨hlate, ht.2⟩
  · apply le_trans _ (hearly x t ⟨ht.1, (lt_of_not_ge hlate).le⟩)
    apply (div_le_iff₀ hden).2
    exact (min_le_right A⁻¹ (B * τ)).trans
      (mul_le_mul_of_nonneg_left (by linarith) hB.le)
