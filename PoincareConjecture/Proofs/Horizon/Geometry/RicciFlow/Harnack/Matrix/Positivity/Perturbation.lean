import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith











set_option autoImplicit false

namespace Poincare.RicciFlow.Harnack


lemma quadratic_perturbation_pos
    {q u w C α δ : ℝ} (hδ : 0 < δ)
    (hα : C + C ^ 2 / (2 * δ) < α)
    (hlower : -C * w ^ 2 - C * u * w ≤ q)
    (hnonzero : u ≠ 0 ∨ w ≠ 0) :
    0 < q + α * w ^ 2 + δ * u ^ 2 := by
  have hgap : C ^ 2 < (α - C) * (2 * δ) :=
    (div_lt_iff₀ (mul_pos (by norm_num) hδ)).mp (by linarith only [hα])
  have hbound :
      ((2 * δ * (α - C) - C ^ 2) * w ^ 2 + δ ^ 2 * u ^ 2) ≤
        2 * δ * (q + α * w ^ 2 + δ * u ^ 2) := by
    have h := mul_le_mul_of_nonneg_left hlower hδ.le
    nlinarith only [h, sq_nonneg (δ * u - C * w)]
  have hpositive : 0 < (2 * δ * (α - C) - C ^ 2) * w ^ 2 + δ ^ 2 * u ^ 2 := by
    rcases hnonzero with hu | hw
    · have hp := mul_pos (sq_pos_of_pos hδ) (sq_pos_of_ne_zero hu)
      have hn := mul_nonneg (show 0 ≤ 2 * δ * (α - C) - C ^ 2 by linarith)
        (sq_nonneg w)
      linarith only [hp, hn]
    · have hp := mul_pos (show 0 < 2 * δ * (α - C) - C ^ 2 by linarith)
        (sq_pos_of_ne_zero hw)
      have hn := mul_nonneg (sq_nonneg δ) (sq_nonneg u)
      linarith only [hp, hn]
  exact pos_of_mul_pos_right (hpositive.trans_le hbound) (by positivity)



lemma exists_initial_time_quadratic_perturbation_pos
    {C ε δ : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t ∈ Set.Ioc 0 t₀,
      ∀ q u w α ψ : ℝ,
        -C * w ^ 2 - C * u * w ≤ q → u ≠ 0 ∨ w ≠ 0 →
        ε / t ≤ α → δ ≤ ψ → 0 < q + α * w ^ 2 + ψ * u ^ 2 := by
  let B := C + C ^ 2 / (2 * δ) + 1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨ε / B, div_pos hε hB, ?_⟩
  intro t ht q u w α ψ hlower hnonzero hα hψ
  have hBt : B * t ≤ ε := by
    have h := (le_div_iff₀ hB).mp ht.2
    linarith only [h]
  have hBα : B ≤ α := ((le_div_iff₀ ht.1).mpr hBt).trans hα
  have hp := quadratic_perturbation_pos hδ
    (show C + C ^ 2 / (2 * δ) < α by dsimp [B] at hBα; linarith)
    hlower hnonzero
  have hψu := mul_le_mul_of_nonneg_right hψ (sq_nonneg u)
  linarith only [hp, hψu]

end Poincare.RicciFlow.Harnack
