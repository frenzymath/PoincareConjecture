import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

open Set
namespace Poincare.CurvatureIntegral

theorem directional_tube_budget_of_explicit_parameters
    {ε C δ r : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hC : 0 ≤ C) (_hδ : 0 ≤ δ) (hδsmall : δ ≤ (ε / 32) ^ 2)
    (hr : 0 < r) (hrsmall : r ≤ ε / (32 * (C + 1))) :
    let q := ε / 64 * r
    let σ := ε ^ 2 / 2048
    0 < q ∧ δ ≤ ε ∧
      4 * Real.sqrt δ + 3 * q / r + 2 * C * r + σ ^ 2 / 8 ≤ ε / 2 := by
  dsimp only
  have hsqrt : Real.sqrt δ ≤ ε / 32 := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity, hδsmall⟩
  have hδle : δ ≤ ε := by nlinarith
  have hCr : 2 * C * r ≤ ε / 16 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 32 * (C + 1))).mp hrsmall
    nlinarith
  have hσ : 0 ≤ ε ^ 2 / 2048 := by positivity
  have hσle : ε ^ 2 / 2048 ≤ ε / 2048 := by nlinarith
  have hσone : ε ^ 2 / 2048 ≤ 1 := by nlinarith
  have hσσ : (ε ^ 2 / 2048) ^ 2 / 8 ≤ ε / 16 := by nlinarith
  have hq : 3 * (ε / 64 * r) / r = 3 * ε / 64 := by field_simp
  refine ⟨by positivity, hδle, ?_⟩
  rw [hq]
  nlinarith

theorem exists_pos_directional_tube_parameters
    {ε C : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C) :
    ∃ δ₀ μ r₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ ε ∧ 0 < μ ∧
      0 < r₀ ∧ r₀ ≤ 1 ∧
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ δ₀ →
      ∀ r : ℝ, 0 < r → r ≤ r₀ →
        4 * Real.sqrt δ + 3 * (μ * r) / r + 2 * C * r +
          (ε ^ 2 / 2048) ^ 2 / 8 ≤ ε / 2 := by
  refine ⟨(ε / 32) ^ 2, ε / 64, min 1 (ε / (32 * (C + 1))),
    by positivity, by nlinarith, by positivity, by positivity, min_le_left _ _, ?_⟩
  intro δ hδ hδsmall r hr hrsmall
  exact (directional_tube_budget_of_explicit_parameters hε hε1 hC hδ hδsmall hr
    (hrsmall.trans (min_le_right _ _))).2.2

theorem tilted_slab_inner_margin_of_small_parameter
    {k : ℕ} {Δ δ r : ℝ} (hΔ : 0 < Δ)
    (hsmall : Δ ≤ 1 / (16 * ((k : ℝ) + 1)))
    (_hδ : 0 ≤ δ)
    (hδsmall : δ ≤ ((Δ / (8 * ((k : ℝ) + 1))) / 256) ^ 2)
    (hr : 0 < r) :
    let ε := Δ / (8 * ((k : ℝ) + 1))
    let σ := ε ^ 2 / 2048
    let τ := 1 / (1 + σ ^ 2 / 8)
    4 * (Δ / 4) * Real.sqrt δ * r ≤ (τ * r / 1024) / 256 := by
  let ε := Δ / (8 * ((k : ℝ) + 1))
  let σ := ε ^ 2 / 2048
  let τ := 1 / (1 + σ ^ 2 / 8)
  change 4 * (Δ / 4) * Real.sqrt δ * r ≤ (τ * r / 1024) / 256
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hΔ16 : Δ ≤ 1 / 16 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 16 * ((k : ℝ) + 1))).mp hsmall
    nlinarith [mul_nonneg hk hΔ.le]
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hεeq : ε * (8 * ((k : ℝ) + 1)) = Δ := by
    dsimp [ε]
    exact div_mul_cancel₀ _ (by positivity)
  have hε128 : ε ≤ 1 / 128 := by nlinarith [mul_nonneg hε hk]
  have hσ : 0 ≤ σ := by dsimp [σ]; positivity
  have hσ1 : σ ≤ 1 := by dsimp [σ]; nlinarith
  have hτ : 3 / 4 ≤ τ := by
    dsimp [τ]
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  have hroot : Real.sqrt δ ≤ 1 / 32768 := by
    have hh : Real.sqrt δ ≤ ε / 256 :=
      (Real.sqrt_le_iff).mpr ⟨by positivity, hδsmall⟩
    linarith
  have hp : Δ * Real.sqrt δ ≤ 1 / 524288 := by
    nlinarith [mul_le_mul hΔ16 hroot (Real.sqrt_nonneg δ)
      (by norm_num : (0 : ℝ) ≤ 1 / 16)]
  have hpr := mul_le_mul_of_nonneg_right hp hr.le
  have htr := mul_le_mul_of_nonneg_right hτ hr.le
  nlinarith

theorem exists_tilted_slab_parameters_with_uniform_tolerance
    {k : ℕ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hΔsmall : Δ ≤ 1 / (16 * ((k : ℝ) + 1))) :
    let ε := Δ / (8 * ((k : ℝ) + 1))
    let σ := ε ^ 2 / 2048
    let τ := 1 / (1 + σ ^ 2 / 8)
    ∃ δ₀ μ η : ℝ, 0 < δ₀ ∧ 0 < μ ∧ 0 < η ∧
      ∀ C : ℝ, 0 ≤ C →
      ∃ r₀ H : ℝ, 0 < r₀ ∧ r₀ ≤ 1 / 2 ∧ 0 ≤ H ∧
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ δ₀ → ∀ r : ℝ, 0 < r → r ≤ r₀ →
        δ ≤ (ε / 256) ^ 2 ∧ δ ≤ ε ∧
        (4 * Real.sqrt δ + 3 * (μ * r) / r + 2 * C * r + σ ^ 2 / 8 ≤ ε / 2) ∧
        4 * (Δ / 4) * Real.sqrt δ * r ≤ (τ * r / 1024) / 256 ∧
        min ((τ * r / 1024) / 96) ((μ * r) / 2) = η * r ∧
        max C (3 / (τ * r / 1024)) ≤ H / r := by
  dsimp only
  let ε := Δ / (8 * ((k : ℝ) + 1))
  let σ := ε ^ 2 / 2048
  let τ := 1 / (1 + σ ^ 2 / 8)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1 := by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have hh := (le_div_iff₀ (by positivity : 0 < 16 * ((k : ℝ) + 1))).mp hΔsmall
    have heq : ε * (8 * ((k : ℝ) + 1)) = Δ := by
      dsimp [ε]; exact div_mul_cancel₀ _ (by positivity)
    nlinarith [mul_nonneg hk hΔ.le, mul_nonneg hk hε.le]
  have hτ : 0 < τ := by dsimp [τ]; positivity
  let μ := ε / 64
  let η := min (τ / 98304) (μ / 2)
  refine ⟨(ε / 256) ^ 2, μ, η, by positivity, by dsimp [μ]; positivity,
    by dsimp [η, μ]; positivity, ?_⟩
  intro C hC
  let r₀ := min (1 / 2) (ε / (32 * (C + 1)))
  let H := max C (3072 / τ)
  refine ⟨r₀, H, by dsimp [r₀]; positivity, min_le_left _ _,
    le_max_of_le_left hC, ?_⟩
  intro δ hδ hδsmall r hr hrsmall
  have hr1 : r ≤ 1 := (hrsmall.trans (min_le_left _ _)).trans (by norm_num)
  have hδ32 : δ ≤ (ε / 32) ^ 2 := by nlinarith
  have hbudget := directional_tube_budget_of_explicit_parameters hε hε1 hC hδ
    hδ32 hr (hrsmall.trans (min_le_right _ _))
  refine ⟨hδsmall, hbudget.2.1, hbudget.2.2,
    tilted_slab_inner_margin_of_small_parameter hΔ hΔsmall hδ hδsmall hr, ?_, ?_⟩
  · change min ((τ * r / 1024) / 96) ((μ * r) / 2) = min (τ / 98304) (μ / 2) * r
    rw [min_mul_of_nonneg _ _ hr.le]
    congr 1 <;> ring
  · apply max_le
    · apply (le_div_iff₀ hr).mpr
      exact (mul_le_of_le_one_right hC hr1).trans (le_max_left _ _)
    · have heq : 3 / (τ * r / 1024) = (3072 / τ) / r := by field_simp; norm_num
      rw [heq]
      exact div_le_div_of_nonneg_right (le_max_right _ _) hr.le

theorem exists_uniform_tilted_slab_parameters
    {k : ℕ} {Δ C : ℝ} (hΔ : 0 < Δ)
    (hΔsmall : Δ ≤ 1 / (16 * ((k : ℝ) + 1))) (hC : 0 ≤ C) :
    let ε := Δ / (8 * ((k : ℝ) + 1))
    let σ := ε ^ 2 / 2048
    let τ := 1 / (1 + σ ^ 2 / 8)
    ∃ δ₀ μ r₀ η H : ℝ,
      0 < δ₀ ∧ 0 < μ ∧ 0 < r₀ ∧ r₀ ≤ 1 / 2 ∧ 0 < η ∧ 0 ≤ H ∧
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ δ₀ → ∀ r : ℝ, 0 < r → r ≤ r₀ →
        δ ≤ (ε / 256) ^ 2 ∧ δ ≤ ε ∧
        (4 * Real.sqrt δ + 3 * (μ * r) / r + 2 * C * r + σ ^ 2 / 8 ≤ ε / 2) ∧
        4 * (Δ / 4) * Real.sqrt δ * r ≤ (τ * r / 1024) / 256 ∧
        min ((τ * r / 1024) / 96) ((μ * r) / 2) = η * r ∧
        max C (3 / (τ * r / 1024)) ≤ H / r := by
  obtain ⟨δ₀, μ, η, hδ₀, hμ, hη, hparams⟩ :=
    exists_tilted_slab_parameters_with_uniform_tolerance hΔ hΔsmall
  obtain ⟨r₀, H, hr₀, hr₀half, hH, hbounds⟩ := hparams C hC
  exact ⟨δ₀, μ, r₀, η, H, hδ₀, hμ, hr₀, hr₀half, hη, hH, hbounds⟩
end Poincare.CurvatureIntegral
