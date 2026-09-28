import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace PoincareConjecture.M65

theorem exists_positive_grid_step {a T epsilon : ℝ} (haT : a < T) (hepsilon : 0 < epsilon) :
    ∃ n : ℕ, ∃ step : ℝ, 0 < step ∧ step < epsilon ∧ a + ((n : ℝ) + 2) * step = T := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((T - a) / epsilon)
  have hden : 0 < (n : ℝ) + 2 := by positivity
  let step := (T - a) / ((n : ℝ) + 2)
  refine ⟨n, step, div_pos (sub_pos.mpr haT) hden, ?_, ?_⟩
  · apply (div_lt_iff₀ hden).mpr
    have h := (div_lt_iff₀ hepsilon).mp hn
    nlinarith
  · dsimp [step]
    field_simp
    ring

end PoincareConjecture.M65
